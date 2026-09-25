module Combinator.Term
  ( Term, Symbol(..), TermView(..), TermError(..), Pos
  , var, constant, (@@), apps, view, foldTerm
  , toRewriting, fromRewriting, mapVariables, mapConstants
  , variables, constants, occurrences, nodeCount, leafCount, exceedsNodes
  , subtermAt, replaceAt, positions, prefixBefore, spine, outerPrefix
  , takeNatural
  ) where

import Combinator.Internal.Term (Symbol(..), Term(..))
import Data.Rewriting.Pos (Pos)
import qualified Data.Rewriting.Term.Type as R
import qualified Data.Rewriting.Term.Ops as RO
import Numeric.Natural (Natural)

-- | View a term as a variable, constant, or application.
data TermView c v
  = Variable v
  | Combinator c
  | Apply (Term c v) (Term c v)
  deriving (Eq, Ord, Show)

-- | Report an invalid application or constant arity at a term position.
data TermError = BadApplicationArity Pos Int | BadConstantArity Pos Int
  deriving (Eq, Show)

-- | Construct an object-language variable.
var :: v -> Term c v
var = Term . R.Var

-- | Construct a combinator constant.
constant :: c -> Term c v
constant c = Term (R.Fun (Constant c) [])

infixl 9 @@
-- | Apply one term to another, associating to the left.
(@@) :: Term c v -> Term c v -> Term c v
Term a @@ Term b = Term (R.Fun Application [a,b])

-- | Apply a term to a list of arguments from left to right.
apps :: Term c v -> [Term c v] -> Term c v
apps = foldl (@@)

-- | Return the outermost variable, constant, or application of a term.
view :: Term c v -> TermView c v
view (Term (R.Var v)) = Variable v
view (Term (R.Fun (Constant c) [])) = Combinator c
view (Term (R.Fun Application [a,b])) = Apply (Term a) (Term b)
view _ = error "Combinator.Term: internal arity invariant violated"

-- | Fold a term using handlers for variables, constants, and applications.
foldTerm :: (v -> a) -> (c -> a) -> (a -> a -> a) -> Term c v -> a
foldTerm f g h (Term t) = R.fold f algebra t
  where
    algebra (Constant c) [] = g c
    algebra Application [a,b] = h a b
    algebra _ _ = error "Combinator.Term: internal arity invariant violated"

-- | Convert a term to the first-order representation used by @term-rewriting@.
toRewriting :: Term c v -> R.Term (Symbol c) v
toRewriting = unTerm

-- | Import a first-order term, rejecting invalid application or constant arities.
fromRewriting :: R.Term (Symbol c) v -> Either TermError (Term c v)
fromRewriting t = check [] t >> pure (Term t)
  where
    check _ (R.Var _) = Right ()
    check _ (R.Fun (Constant _) []) = Right ()
    check p (R.Fun Application [a,b]) =
      check (p ++ [0]) a >> check (p ++ [1]) b
    check p (R.Fun Application xs) = Left (BadApplicationArity p (length xs))
    check p (R.Fun (Constant _) xs) = Left (BadConstantArity p (length xs))

-- | Map variable names while preserving constants and application structure.
mapVariables :: (v -> w) -> Term c v -> Term c w
mapVariables f = Term . R.map id f . unTerm

-- | Map constant names while preserving variables and application structure.
mapConstants :: (c -> d) -> Term c v -> Term d v
mapConstants f = Term . R.map rename id . unTerm
  where
    rename Application = Application
    rename (Constant c) = Constant (f c)

-- | List variable occurrences from left to right, including repetitions.
variables :: Term c v -> [v]
variables = RO.vars . unTerm

-- | List constant occurrences from left to right, including repetitions.
constants :: Term c v -> [c]
constants t = [c | Constant c <- RO.funs (unTerm t)]

-- | Count occurrences of a variable in the term tree.
occurrences :: Eq v => v -> Term c v -> Natural
occurrences x = foldTerm (\v -> if v == x then 1 else 0) (const 0) (+)

-- | Count all variable, constant, and application nodes in the term tree.
nodeCount :: Term c v -> Natural
nodeCount = foldTerm (const 1) (const 1) (\a b -> 1+a+b)

-- | Count variable and constant leaves in the term tree.
leafCount :: Term c v -> Natural
leafCount = foldTerm (const 1) (const 1) (+)

-- | Check whether the term tree exceeds a node bound, stopping once exceeded.
exceedsNodes :: Natural -> Term c v -> Bool
exceedsNodes bound t = go bound [unTerm t]
  where
    go _ [] = False
    go 0 (_:_) = True
    go n (R.Var _ : ts) = go (n-1) ts
    go n (R.Fun _ xs : ts) = go (n-1) (xs ++ ts)

-- | Return the subtree at a position, or 'Nothing' for an invalid position.
subtermAt :: Term c v -> Pos -> Maybe (Term c v)
subtermAt t p = Term <$> RO.subtermAt (unTerm t) p

-- | Replace the subtree at a position, or return 'Nothing' for an invalid position.
replaceAt :: Term c v -> Pos -> Term c v -> Maybe (Term c v)
replaceAt t p u = Term <$> RO.replaceAt (unTerm t) p (unTerm u)

-- | List all subtree positions in preorder.
positions :: Term c v -> [Pos]
positions t = [] : case view t of
  Apply a b -> map (0:) (positions a) ++ map (1:) (positions b)
  _ -> []

-- | Count occurrences of a variable before the subtree at a valid position.
prefixBefore :: Eq v => v -> Term c v -> Pos -> Maybe Natural
prefixBefore _ _ [] = Just 0
prefixBefore x t (d:ds) = case (d, view t) of
  (0, Apply a _) -> prefixBefore x a ds
  (1, Apply a b) -> (occurrences x a +) <$> prefixBefore x b ds
  _ -> Nothing

-- | Split an application into its head and arguments in left-to-right order.
spine :: Term c v -> (Term c v, [Term c v])
spine t = go t []
  where
    go u args = case view u of
      Apply a b -> go a (b:args)
      _ -> (u,args)

-- | Construct @x (x (... u))@ with the given number of outer applications of @x@.
outerPrefix :: Natural -> v -> Term c v -> Term c v
outerPrefix 0 _ t = t
outerPrefix n x t = var x @@ outerPrefix (n-1) x t

-- | Take a list prefix whose length is bounded by a 'Natural'.
takeNatural :: Natural -> [a] -> [a]
takeNatural 0 _ = []
takeNatural _ [] = []
takeNatural n (a:as) = a : takeNatural (n-1) as
