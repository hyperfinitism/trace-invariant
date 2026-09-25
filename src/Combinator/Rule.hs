module Combinator.Rule
  ( Rule, RuleError(..), ruleSymbol, ruleArity, ruleBody
  , mkRule, argumentMultiplicity, duplicatedArguments, toRewriteRule
  , Basis, BasisError(..), mkBasis, extendBasis, basisRules, basisSymbols
  , lookupRule, validateTerm
  , bRule, cRule, iRule, mRule, wRule, sRule
  , basisBMI, basisBWI, basisBCIMW, basisBCIMWS, namedBasis
  ) where

import Combinator.Term
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Rewriting.Rule.Type as R
import Numeric.Natural (Natural)

-- | Represent a validated non-erasing reduction rule.
data Rule c = Rule c Int (Term c Int)
  deriving (Eq, Ord, Show)

-- | Return the head constant reduced by a rule.
ruleSymbol :: Rule c -> c
ruleSymbol (Rule c _ _) = c

-- | Return the number of arguments required by a rule.
ruleArity :: Rule c -> Int
ruleArity (Rule _ n _) = n

-- | Return the rule's right-hand side with one-based argument metavariables.
ruleBody :: Rule c -> Term c Int
ruleBody (Rule _ _ body) = body

-- | Report invalid arities, undeclared arguments, or erased arguments.
data RuleError
  = NonPositiveArity Int
  | ArgumentOutOfRange Int
  | ErasedArgument Int
  deriving (Eq, Show)

-- | Construct a positive-arity rule in which every declared argument occurs.
mkRule :: c -> Int -> Term c Int -> Either RuleError (Rule c)
mkRule c n body
  | n <= 0 = Left (NonPositiveArity n)
  | otherwise = case filter (\i -> i < 1 || i > n) (variables body) of
      i:_ -> Left (ArgumentOutOfRange i)
      [] -> case filter (\i -> occurrences i body == 0) [1..n] of
        i:_ -> Left (ErasedArgument i)
        [] -> Right (Rule c n body)

-- | Count an argument's occurrences in the rule's right-hand side.
argumentMultiplicity :: Rule c -> Int -> Natural
argumentMultiplicity r i = occurrences i (ruleBody r)

-- | List duplicated argument indices and their multiplicities in index order.
duplicatedArguments :: Rule c -> [(Int, Natural)]
duplicatedArguments r =
  [(i,n) | i <- [1..ruleArity r], let n = argumentMultiplicity r i, n >= 2]

-- | Convert a combinator rule to a first-order rewrite rule.
toRewriteRule :: Rule c -> R.Rule (Symbol c) Int
toRewriteRule r = R.Rule
  (toRewriting (apps (constant (ruleSymbol r)) (map var [1..ruleArity r])))
  (toRewriting (ruleBody r))

-- | Represent a set of rules with one rule per head constant.
newtype Basis c = Basis (Map.Map c (Rule c))
  deriving (Eq, Ord, Show)

-- | Report duplicate symbols or unregistered constants.
data BasisError c
  = DuplicateSymbol c
  | UnregisteredRHSConstant c
  | UnregisteredTermConstants [c]
  deriving (Eq, Show)

-- | Construct a basis, rejecting duplicate heads and unregistered right-hand constants.
mkBasis :: Ord c => [Rule c] -> Either (BasisError c) (Basis c)
mkBasis rs = do
  m <- add Map.empty rs
  case [c | r <- rs, c <- constants (ruleBody r), Map.notMember c m] of
    c:_ -> Left (UnregisteredRHSConstant c)
    [] -> Right (Basis m)
  where
    add m [] = Right m
    add m (r:rest)
      | Map.member (ruleSymbol r) m = Left (DuplicateSymbol (ruleSymbol r))
      | otherwise = add (Map.insert (ruleSymbol r) r m) rest

-- | Add rules to a basis, rejecting duplicate heads and unregistered constants.
extendBasis :: Ord c => Basis c -> [Rule c] -> Either (BasisError c) (Basis c)
extendBasis b rs = mkBasis (basisRules b ++ rs)

-- | List the rules of a basis in symbol order.
basisRules :: Basis c -> [Rule c]
basisRules (Basis m) = Map.elems m

-- | List the registered constants of a basis in symbol order.
basisSymbols :: Basis c -> [c]
basisSymbols (Basis m) = Map.keys m

-- | Look up the reduction rule for a constant.
lookupRule :: Ord c => c -> Basis c -> Maybe (Rule c)
lookupRule c (Basis m) = Map.lookup c m

-- | Check that every constant in a term belongs to the basis.
validateTerm :: Ord c => Basis c -> Term c v -> Either (BasisError c) ()
validateTerm (Basis m) t = case
  Set.toAscList (Set.fromList (filter (`Map.notMember` m) (constants t))) of
    [] -> Right ()
    cs -> Left (UnregisteredTermConstants cs)

-- | Provide the bluebird rule: @B x y z -> x (y z)@.
bRule :: Rule String
bRule = Rule "B" 3 (var 1 @@ (var 2 @@ var 3))
-- | Provide the cardinal rule: @C x y z -> x z y@.
cRule :: Rule String
cRule = Rule "C" 3 (var 1 @@ var 3 @@ var 2)
-- | Provide the identity rule: @I x -> x@.
iRule :: Rule String
iRule = Rule "I" 1 (var 1)
-- | Provide the mockingbird rule: @M x -> x x@.
mRule :: Rule String
mRule = Rule "M" 1 (var 1 @@ var 1)
-- | Provide the warbler rule: @W x y -> x y y@.
wRule :: Rule String
wRule = Rule "W" 2 (var 1 @@ var 2 @@ var 2)
-- | Provide the starling rule: @S x y z -> x z (y z)@.
sRule :: Rule String
sRule = Rule "S" 3 ((var 1 @@ var 3) @@ (var 2 @@ var 3))

-- | Provide the basis containing B, M, and I.
basisBMI :: Basis String
basisBMI = fixed [bRule,mRule,iRule]
-- | Provide the basis containing B, W, and I.
basisBWI :: Basis String
basisBWI = fixed [bRule,wRule,iRule]
-- | Provide the basis containing B, C, I, M, and W.
basisBCIMW :: Basis String
basisBCIMW = fixed [bRule,cRule,iRule,mRule,wRule]
-- | Provide the basis containing B, C, I, M, W, and S.
basisBCIMWS :: Basis String
basisBCIMWS = fixed [bRule,cRule,iRule,mRule,wRule,sRule]

fixed :: [Rule String] -> Basis String
fixed rs = case mkBasis rs of
  Right b -> b
  Left e -> error ("Combinator.Rule: invalid built-in basis: " ++ show e)

-- | Construct a basis from built-in constant names, rejecting unknown or repeated names.
namedBasis :: [String] -> Either String (Basis String)
namedBasis names = do
  rs <- traverse findRule names
  either (Left . show) Right (mkBasis rs)
  where
    findRule c = maybe (Left ("Unknown built-in symbol: " ++ c)) Right
      (lookupRule c basisBCIMWS)
