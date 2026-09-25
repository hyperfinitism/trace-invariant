module Main (main) where

import Combinator
import Examples
import Enumeration
import Reference
import Test.Tasty (defaultMain, testGroup, TestTree)
import Test.Tasty.HUnit
import qualified Test.Tasty.QuickCheck as TQ
import Test.QuickCheck (Gen, sized, elements, frequency, chooseInt, forAll, (===))
import qualified Data.Rewriting.Term.Type as Raw
import qualified Data.Map.Strict as Map
import Data.List (isPrefixOf)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Either (isLeft)
import Numeric.Natural (Natural)

main :: IO ()
main = defaultMain (testGroup "combinator-trace"
  [ termTests, ruleTests, reductionTests, traceTests, streamTests
  , invariantTests, exampleTests, enumerationTests, propertyTests ])

must :: Show e => Either e a -> a
must = either (error . show) id

parse :: String -> Term String String
parse = must . parseTerm

nonUniformF, omega :: Term String String
nonUniformF = parse "M(BxM)"
omega = parse "MM"

run :: Basis String -> Observer String -> Limits -> String -> RunResult String String
run b o limits = must . runTrace b o "x" limits . parse

shortLimits :: Limits
shortLimits = defaultLimits
  { maxSteps = Just 1000, maxEvents = Just 12, maxNodes = Just 100000 }

point :: Natural -> Natural -> TracePoint
point = TracePoint

termTests :: TestTree
termTests = testGroup "terms and syntax"
  [ testCase "compact syntax and left association" $
      parse "Bxyz" @?= apps (constant "B") (map var ["x","y","z"])
  , testCase "right application parentheses" $
      parse "x(yz)" @?= var "x" @@ (var "y" @@ var "z")
  , testCase "long names and escapes round trip" $ do
      let t = constant "D]\\name" @@ var "x}\\name" @@ constant ""
      parseTerm (renderNamedTerm t) @?= Right t
  , testCase "malformed syntax is rejected" $
      assertBool "unclosed parentheses" (isLeft (parseTerm "B(x"))
  , testCase "empty input is rejected" $
      assertBool "empty input" (isLeft (parseTerm ""))
  , testCase "safe raw import rejects wrong application arity" $
      fromRewriting (Raw.Fun Application [Raw.Var "x"]
        :: Raw.Term (Symbol String) String) @?= Left (BadApplicationArity [] 1)
  , testCase "safe raw import rejects applied constants" $
      fromRewriting (Raw.Fun (Constant "M") [Raw.Var "x"])
        @?= Left (BadConstantArity [] 1)
  , testCase "shared values count twice by occurrence" $ do
      let a = parse "x(yx)"
      occurrences "x" (a @@ a) @?= 4
      nodeCount (a @@ a) @?= 11
  , testCase "replacement affects one occurrence" $ do
      let t = parse "(Ix)(Ix)"
      replaceAt t [0] (var "z") @?= Just (parse "z(Ix)")
  , testCase "invalid positions fail safely" $ do
      subtermAt (parse "xy") [2] @?= Nothing
      prefixBefore "x" (parse "xy") [-1] @?= Nothing
  , testCase "outer prefix is right nested" $
      outerPrefix 3 "x" (var "y" :: Term String String) @?= parse "x(x(xy))"
  , testCase "node guard is inclusive" $ do
      assertBool "three nodes fit" (not (exceedsNodes 3 (parse "xy")))
      assertBool "two nodes do not fit" (exceedsNodes 2 (parse "xy"))
  ]

ruleTests :: TestTree
ruleTests = testGroup "rule registration"
  [ testCase "built-ins validate through the public constructor" $
      mapM_ (\r -> mkRule (ruleSymbol r) (ruleArity r) (ruleBody r) @?= Right r)
        (basisRules basisBCIMWS)
  , testCase "S metadata identifies the third argument" $
      duplicatedArguments sRule @?= [(3,2)]
  , testCase "erasing rules are rejected" $
      mkRule "K" 2 (var 1) @?= Left (ErasedArgument 2)
  , testCase "new metavariables are rejected" $
      mkRule "D" 1 (var 2) @?= Left (ArgumentOutOfRange 2)
  , testCase "arity must be positive" $
      mkRule "D" 0 (var 1) @?= Left (NonPositiveArity 0)
  , testCase "duplicate rules are rejected" $
      mkBasis [mRule,mRule] @?= Left (DuplicateSymbol "M")
  , testCase "RHS constants must be registered" $ do
      let j = must (mkRule "J" 1 (constant "I" @@ var 1))
      mkBasis [j] @?= Left (UnregisteredRHSConstant "I")
      assertBool "registered I permits the macro" (not (isLeft (mkBasis [iRule,j])))
  , testCase "S can be added without changing the engine" $ do
      let bs = must (extendBasis basisBCIMW [sRule])
      resultTerm (run bs sObserver shortLimits "SIIx") @?= parse "xx"
  , testCase "non-duplicated argument selectors are rejected" $
      validateObserver basisBMI (selectedArguments [("B",1)])
        @?= Left (NotADuplicatedArgument "B" 1)
  , testCase "unknown selectors are rejected" $
      validateObserver basisBMI sObserver @?= Left (UnknownObservedSymbol "S")
  ]

reductionTests :: TestTree
reductionTests = testGroup "rewriting semantics"
  [ testCase "MM is a contraction despite equal terms" $ do
      case stepLI basisBMI omega of
        Nothing -> assertFailure "MM must have a redex"
        Just st -> do
          stepAfter st @?= omega
          stepPosition st @?= []
      assertBool "not normal" (not (isNormal basisBMI omega))
  , testCase "LI visits the argument before M" $ do
      let t = parse "M(Ix)"
      fmap stepPosition (stepLI basisBMI t) @?= Just [1]
      fmap (ruleSymbol . stepRule) (stepLI basisBMI t) @?= Just "I"
  , testCase "overapplication is a nested exact-arity contraction" $ do
      let st = stepLI basisBMI (parse "Ixy")
      fmap stepPosition st @?= Just [0]
      fmap stepAfter st @?= Just (parse "xy")
  , testCase "weak contraction can differ from LI" $ do
      let t = parse "M(Ix)"
      fmap stepAfter (contractAt basisBMI t []) @?= Just (parse "(Ix)(Ix)")
      map stepPosition (weakSteps basisBMI t) @?= [[],[1]]
  , testCase "C swaps its last two arguments" $
      fmap stepAfter (stepLI basisBCIMW (parse "Cxyz")) @?= Just (parse "xzy")
  , testCase "all weak reducts of a terminating example have the same normal form" $ do
      let reducts = weakSteps basisBMI (parse "M(Ix)")
      mapM_ (\st -> do
        let r = must (runTrace basisBMI mObserver "x" shortLimits (stepAfter st))
        resultStop r @?= NormalForm
        resultTerm r @?= parse "xx") reducts
  ]

traceTests :: TestTree
traceTests = testGroup "bounded observations"
  [ testCase "W p is before the redex, not before its second argument" $ do
      resultPoints (run basisBWI wObserver shortLimits "Wxx") @?= [point 1 0]
      resultPoints (run basisBWI wObserver shortLimits "x(Wxx)") @?= [point 1 1]
  , testCase "S observes only argument three" $
      resultPoints (run basisBCIMWS sObserver shortLimits "Sxxx") @?= [point 1 0]
  , testCase "zero q observations are retained" $
      resultPoints (run basisBMI mObserver shortLimits "MM") @?= replicate 12 (point 0 0)
  , testCase "step budget is distinct from normality" $ do
      let r = run basisBMI mObserver (shortLimits { maxSteps = Just 3 }) "MM"
      resultStop r @?= StepBudgetReached
      resultSteps r @?= 3
  , testCase "the default step budget stops a loop with no selected events" $ do
      let r = run basisBCIMW wObserver defaultLimits "MM"
      resultStop r @?= StepBudgetReached
      resultSteps r @?= 10000
      resultEvents r @?= []
  , testCase "an explicit step budget stops the growing term with an unreachable observer" $ do
      let y = must (mkRule "Y" 1 (var 1 @@ (constant "Y" @@ var 1)))
          bs = must (extendBasis basisBMI [y])
          observer = selectedArguments [("Y",1)]
          r = run bs observer (defaultLimits { maxSteps = Just 12, maxEvents = Just 6 }) "M(BxM)"
      resultStop r @?= StepBudgetReached
      resultSteps r @?= 12
      resultEvents r @?= []
      resultTerm r @?= outerPrefix 6 "x" nonUniformF
  , testCase "normal input resolves at a zero step budget" $
      resultStop (run basisBMI mObserver (shortLimits { maxSteps = Just 0 }) "x") @?= NormalForm
  , testCase "normal form after final allowed event is recognised" $
      resultStop (run basisBMI mObserver (shortLimits { maxEvents = Just 1 }) "Mx") @?= NormalForm
  , testCase "zero event budget commits no contraction" $ do
      let r = run basisBMI mObserver (shortLimits { maxEvents = Just 0 }) "MM"
      resultStop r @?= EventBudgetReached
      resultSteps r @?= 0
  , testCase "node bound rejects the next step atomically" $ do
      let r = run basisBMI mObserver (shortLimits { maxNodes = Just 5 }) "M(xy)"
      resultStop r @?= NodeBudgetReached
      resultTerm r @?= parse "M(xy)"
      resultSteps r @?= 0
      resultEvents r @?= []
  , testCase "unknown constants are not silently accepted in a run" $
      assertBool "C is outside BMI"
        (isLeft (runTrace basisBMI mObserver "x" shortLimits (parse "Cxyz")))
  , testCase "resumption uses cumulative budgets" $ do
      let l5 = shortLimits { maxEvents = Just 5 }
          l12 = shortLimits
          firstRun = must (runTrace basisBMI mObserver "x" l5 nonUniformF)
          resumed = resumeTrace l12 (checkpoint firstRun)
          full = must (runTrace basisBMI mObserver "x" l12 nonUniformF)
      resultEvents resumed @?= resultEvents full
      resultTerm resumed @?= resultTerm full
      resultSteps resumed @?= resultSteps full
      resultStop resumed @?= resultStop full
  , testCase "cycle detection recognises MM" $ do
      let r = run basisBMI mObserver (shortLimits { detectCycles = True }) "MM"
      resultSteps r @?= 1
      case resultStop r of
        RepeatedState loop -> do
          cycleStartStep loop @?= 0
          cycleEndStep loop @?= 1
          map eventPoint (cycleEventBlock loop) @?= [point 0 0]
        other -> assertFailure ("Expected a cycle, got " ++ show other)
  , testCase "an M-only view of a W loop can be finite" $ do
      let r = run basisBCIMW mObserver (shortLimits { detectCycles = True }) "(WI)(WI)"
      case resultStop r of
        RepeatedState loop -> cycleEventBlock loop @?= []
        other -> assertFailure ("Expected a cycle, got " ++ show other)
  , testCase "multiple duplicated arguments produce an atomic event group" $ do
      let d = must (mkRule "D" 3
                ((var 1 @@ var 2) @@ (var 1 @@ var 3) @@ (var 2 @@ var 3)))
          bs = must (mkBasis [d])
          r = run bs allDuplicated shortLimits "Dxyx"
          blocked = run bs allDuplicated (shortLimits { maxEvents = Just 2 }) "Dxyx"
      map eventArgument (resultEvents r) @?= [1,2,3]
      resultPoints r @?= [point 1 0,point 0 0,point 1 0]
      resultStop blocked @?= EventBudgetReached
      resultSteps blocked @?= 0
      resultEvents blocked @?= []
  , testCase "multiplicity does not multiply q" $ do
      let d = must (mkRule "D" 1 (var 1 @@ var 1 @@ var 1))
          bs = must (mkBasis [d])
          r = run bs allDuplicated shortLimits "Dx"
      resultPoints r @?= [point 1 0]
      map eventMultiplicity (resultEvents r) @?= [3]
  , testCase "target variable is parametrised" $ do
      let r = must (runTrace basisBMI mObserver "y" shortLimits (parse "M(yx)"))
      resultPoints r @?= [point 1 0]
  ]

streamTests :: TestTree
streamTests = testGroup "lazy trace streams"
  [ testCase "a normalising trace is finite even with later unobserved steps" $ do
      let events = must (traceStream basisBMI mObserver "x" (parse "MIx"))
      map eventPoint events @?= [point 0 0]
      let prefix = run basisBMI mObserver (defaultLimits { maxEvents = Just 1 }) "MIx"
          complete = run basisBMI mObserver (defaultLimits { maxEvents = Just 2 }) "MIx"
      resultStop prefix @?= EventBudgetReached
      resultStop complete @?= NormalForm
      resultTerm complete @?= parse "x"
      resultEvents complete @?= events
  , testCase "an infinite growing trace yields any requested finite prefix" $ do
      let events = must (traceStream basisBMI mObserver "x" nonUniformF)
      map eventPoint (take 64 events) @?= map (point 1) [0..63]
      map eventStep (take 64 events) @?= [0,2..126]
  , testCase "a periodic reduction produces an infinite event stream" $ do
      let events = must (traceStream basisBMI mObserver "x" omega)
      map eventPoint (take 128 events) @?= replicate 128 (point 0 0)
      map eventStep (take 128 events) @?= [0..127]
  , testCase "the default step budget applies before the event budget" $ do
      let r = run basisBMI mObserver (defaultLimits { maxEvents = Just 10001 }) "MM"
      resultStop r @?= StepBudgetReached
      resultSteps r @?= 10000
      length (resultEvents r) @?= 10000
  , testCase "the step budget can be raised above the default" $ do
      let limits = defaultLimits { maxSteps = Just 10002, maxEvents = Just 10001 }
          r = run basisBMI mObserver limits "MM"
      resultStop r @?= EventBudgetReached
      resultSteps r @?= 10001
      length (resultEvents r) @?= 10001
  , testCase "the library can explicitly remove the step budget" $ do
      let limits = defaultLimits { maxSteps = Nothing, maxEvents = Just 10001 }
          r = run basisBMI mObserver limits "MM"
      resultStop r @?= EventBudgetReached
      resultSteps r @?= 10001
      length (resultEvents r) @?= 10001
  , testCase "invalid stream inputs are rejected before traversal" $ do
      traceStream basisBMI mObserver "x" (parse "Cx")
        @?= Left (InvalidBasisTerm (UnregisteredTermConstants ["C"]))
      traceStream basisBMI sObserver "x" omega
        @?= Left (InvalidObserver (UnknownObservedSymbol "S"))
  ]

resolved :: Analysis String -> Invariant String
resolved (Resolved x) = x
resolved (Unresolved _) = error "Test expected a resolved invariant"

inv :: Theory -> String -> Invariant String
inv theory = resolved . must . analyseInvariant theory "x" shortLimits . parse

invariantTests :: TestTree
invariantTests = testGroup "represented invariant fragment"
  [ testCase "normal forms, not empty traces, determine normal invariants" $
      equalInvariants (inv BMI "x") (inv BMI "y") @?= Right False
  , testCase "a normalising term with trace events has its normal form as invariant" $
      viewInvariant (inv BMI "M(Ix)") @?= NormalInvariant (parse "xx")
  , testCase "MM resolves to its periodic tail class" $
      viewInvariant (inv BMI "MM") @?= PeriodicInvariant (periodicClass (point 0 0 :| []))
  , testCase "transient normalisation before a loop does not change the class" $
      equalInvariants (inv BMI "I(MM)") (inv BMI "MM") @?= Right True
  , testCase "a BWI reduction cycle yields a periodic trace representative" $
      viewInvariant (inv BWI "(WI)(WI)") @?= PeriodicInvariant (periodicClass (point 0 0 :| []))
  , testCase "period phase and a repeated shorter block are quotiented" $ do
      let a = point 1 0; b = point 2 1
      periodicClass (a :| [b,a,b]) @?= periodicClass (b :| [a])
  , testCase "distinct periodic classes remain distinct" $
      assertBool "a positive p shift changes this periodic class"
        (periodicClass (point 0 0 :| []) /= periodicClass (point 0 1 :| []))
  , testCase "incompatible theories are rejected" $
      equalInvariants (inv BMI "x") (inv BWI "x") @?= Left DifferentTheories
  , testCase "incompatible target variables are rejected" $ do
      let a = inv BMI "x"
          b = resolved (must (analyseBMI "y" shortLimits (parse "x")))
      equalInvariants a b @?= Left DifferentTargetVariables
  , testCase "C is excluded by the BMI invariant API" $
      assertBool "unsupported extension"
        (isLeft (analyseBMI "x" shortLimits (parse "Cxyz")))
  , testCase "a growing non-periodic example remains unresolved" $ do
      case must (analyseBMI "x" (shortLimits { maxEvents = Just 5 }) nonUniformF) of
        Unresolved r -> resultStop r @?= EventBudgetReached
        Resolved _ -> assertFailure "No full-state loop or normal form was reached"
  , testCase "star shifts a right trace by the normal left occurrence count" $ do
      let out = resolved (must (starInvariant shortLimits (inv BMI "x") (inv BMI "MM")))
      equalInvariants out (inv BMI "x(MM)") @?= Right True
  , testCase "star with a trace on the left absorbs" $ do
      let out = resolved (must (starInvariant shortLimits (inv BMI "MM") (inv BMI "x")))
      equalInvariants out (inv BMI "MM") @?= Right True
  , testCase "star of two normal forms may create a loop" $ do
      let out = resolved (must (starInvariant shortLimits (inv BMI "M") (inv BMI "M")))
      equalInvariants out (inv BMI "MM") @?= Right True
  ]

exampleTests :: TestTree
exampleTests = testGroup "example files and rewriting boundaries"
  (map check allExamples ++
    [ testCase "C boundary is an actual weak contraction" $
        fmap stepAfter (contractAt basisBCIMW (parse "CI(MM)x") [])
          @?= Just (parse "Ix(MM)")
    , testCase "W can create a redex off the rightmost path" $ do
        let a = parse "W(Bx)"
            after = stepAfter <$> stepLI basisBWI (constant "W" @@ constant "I" @@ a)
        case after of
          Just t -> assertBool "the BWI structural condition fails"
            (not (rightmostCondition basisBWI "x" t))
          Nothing -> assertFailure "Expected W contraction"
    ])
  where
    check ex = testCase (exampleTermFile ex) $ do
      report <- must <$> checkExample 12 ex
      resultPoints (checkedRun report) @?= checkedExpected report
      assertBool "finite formula check" (checkedPassed report)
      case expectedNormalForm ex of
        Nothing -> resultStop (checkedRun report) @?= EventBudgetReached
        Just normalForm -> do
          resultStop (checkedRun report) @?= NormalForm
          resultTerm (checkedRun report) @?= normalForm

enumerationTests :: TestTree
enumerationTests = testGroup "bounded enumeration"
  [ testCase "all closed BMI terms through four leaves are enumerated" $
      length (termsUpToLeaves 4 ["B","M","I"] ([] :: [String])) @?= 471
  , testCase "repeated alphabet entries do not duplicate terms" $
      length (termsWithLeaves 2 ["M","M"] ([] :: [String])) @?= 1
  , testCase "BMI structural lemmas on the enumerated finite runs" $ do
      let r = checkSmallBMI 4 40 5000
      smallCandidateCount r @?= 471
      smallFailures r @?= []
      assertBool "eligible P were checked" (smallEligibleCount r > 0)
      assertBool "M events were inspected" (smallMEvents r > 0)
  ]

genTerm :: Gen (Term String String)
genTerm = sized (go . min 12)
  where
    atom = frequency
      [ (3, constant <$> elements ["B","C","I","M","W","S"])
      , (2, var <$> elements ["x","y","z","long name","a}b","a\\b"]) ]
    go 0 = atom
    go n = frequency
      [ (3, atom)
      , (5, do k <- chooseInt (0,n-1)
               a <- go k
               b <- go (n-1-k)
               pure (a @@ b)) ]

propertyTests :: TestTree
propertyTests = testGroup "property-based differential checks"
  [ TQ.testProperty "pretty/parse round trip" $ forAll genTerm $ \t ->
      parseTerm (renderNamedTerm t) === Right t
  , TQ.testProperty "generic term import/export round trip" $ forAll genTerm $ \t ->
      fromRewriting (toRewriting t) === Right t
  , TQ.testProperty "binary-tree node/leaf relation" $ forAll genTerm $ \t ->
      nodeCount t + 1 === 2 * leafCount t
  , TQ.testProperty "one LI step agrees with the independent reducer" $ forAll genTerm $ \t ->
      fmap production (stepLI basisBCIMWS t) === fmap reference (refLI ["B","C","I","M","W","S"] (toRef t))
  , TQ.testProperty "LI chooses a member of the full weak relation" $ forAll genTerm $ \t ->
      case stepLI basisBCIMWS t of
        Nothing -> null (weakSteps basisBCIMWS t)
        Just st -> any (\u -> stepPosition u == stepPosition st && stepAfter u == stepAfter st)
                     (weakSteps basisBCIMWS t)
  , TQ.testProperty "prefix count agrees with ordered leaf positions" $ forAll genTerm $ \t ->
      let xLeaves = [p | p <- positions t, subtermAt t p == Just (var "x")]
      in all (\p -> prefixBefore "x" t p == Just
              (fromIntegral (length [q | q <- xLeaves, q < p, not (p `isPrefixOf` q)])))
           (positions t)
  , TQ.testProperty "outer x context shifts the observed p coordinates" $ forAll genTerm $ \t ->
      let limits = Limits (Just 6) Nothing Nothing False
          left = must (runTrace basisBCIMWS allDuplicated "x" limits t)
          right = must (runTrace basisBCIMWS allDuplicated "x" limits (outerPrefix 2 "x" t))
      in resultPoints right === map (shiftPoint 2) (resultPoints left)
  , TQ.testProperty "lazy events agree with the bounded runner" $ forAll genTerm $ \t ->
      let limits = Limits (Just 6) Nothing Nothing False
          events = resultEvents (must (runTrace basisBCIMWS allDuplicated "x" limits t))
          stream = must (traceStream basisBCIMWS allDuplicated "x" t)
      in take (length events) stream === events
  ]
  where
    production st = (toRef (stepAfter st), stepPosition st, ruleSymbol (stepRule st),
      map (toRef . snd) (Map.toAscList (stepArguments st)))
    reference st = (refAfter st, refPosition st, refRule st, refArguments st)
