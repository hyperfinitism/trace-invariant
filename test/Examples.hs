module Examples
  ( Example(..), ExampleCheck(..), allExamples, checkExample, checkExamples
  ) where

import Combinator.Term
import Combinator.Rule
import Combinator.Trace
import Combinator.Parser (parseTerm)
import Config (loadExtraRules)
import Data.Bifunctor (first)
import Numeric.Natural (Natural)
import System.IO.Error (tryIOError)

data Example = Example
  { exampleTermFile :: FilePath
  , exampleBasis :: String
  , exampleObserver :: Observer String
  , exampleRulesFile :: Maybe FilePath
  , expectedTrace :: [TracePoint]
  , expectedNormalForm :: Maybe (Term String String)
  }

data ExampleCheck = ExampleCheck
  { checkedName :: String
  , checkedRun :: RunResult String String
  , checkedExpected :: [TracePoint]
  , checkedPassed :: Bool
  } deriving Show

beta :: Natural -> TracePoint
beta = TracePoint 1

alpha :: Natural -> TracePoint
alpha 0 = TracePoint 1 0
alpha n = TracePoint (n+1) (n*(n-1) `div` 2)

allExamples :: [Example]
allExamples =
  [ Example "examples/non-uniform-fp.term" "BMI" mObserver Nothing
      (map beta [0..]) Nothing
  , Example "examples/ns-fpc.term" "BMI" mObserver Nothing
      (map alpha [0..]) Nothing
  , Example "examples/ns-fpc-shifted.term" "BMI" mObserver Nothing
      (map (shiftPoint 1 . alpha) [0..]) Nothing
  , Example "examples/bwi-fpc.term" "BWI" wObserver Nothing
      (beta 0 : map beta [0..]) Nothing
  , Example "examples/bwi-fpc-shifted.term" "BWI" wObserver Nothing
      (map (shiftPoint 1) (beta 0 : map beta [0..])) Nothing
  , Example "examples/bcm-fpc.term" "BCIM" mObserver Nothing
      (map beta [0..]) Nothing
  , Example "examples/bcm-fpc-shifted.term" "BCIM" mObserver Nothing
      (map (shiftPoint 1 . beta) [0..]) Nothing
  , Example "examples/bcis-fpc.term" "BCI" sObserver (Just "examples/custom-s.json")
      (map beta [0..]) Nothing
  , Example "examples/y-fpc.term" "" (selectedArguments [("Y",1)])
      (Just "examples/custom-y.json") (map beta [0..]) Nothing
  , Example "examples/normalising.term" "BMI" mObserver Nothing
      [beta 0] (Just (var "x" @@ var "x"))
  , Example "examples/periodic.term" "BMI" mObserver Nothing
      (repeat (TracePoint 0 2)) Nothing
  ]

checkExample :: Natural -> Example -> IO (Either String ExampleCheck)
checkExample n ex = do
  termText <- tryIOError (readFile (exampleTermFile ex))
  extraRules <- case exampleRulesFile ex of
    Nothing -> pure (Right [])
    Just path -> fmap (first ((path ++ ": ") ++)) (loadExtraRules path)
  pure $ do
    text <- first show termText
    term <- first ((exampleTermFile ex ++ ": ") ++) (parseTerm text)
    base <- namedBasis (map (:[]) (exampleBasis ex))
    rules <- extraRules
    basis <- first show (extendBasis base rules)
    run <- first show $ runTrace basis (exampleObserver ex) "x"
      (defaultLimits { maxSteps = Just 20000, maxEvents = Just n
                     , maxNodes = Just 250000, detectCycles = False }) term
    let expected = takeNatural n (expectedTrace ex)
    pure (ExampleCheck (exampleTermFile ex) run expected (resultPoints run == expected))

checkExamples :: Natural -> IO (Either String [ExampleCheck])
checkExamples n = sequence <$> traverse (checkExample n) allExamples
