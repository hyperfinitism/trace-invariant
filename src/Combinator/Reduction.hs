module Combinator.Reduction
  ( Step, stepBefore, stepAfter, stepPosition, stepRule, stepArguments
  , stepLI, weakSteps, contractAt, isNormal
  ) where

import Combinator.Internal.Term (Term(..))
import Combinator.Term (Symbol, Pos)
import Combinator.Rule
import qualified Data.Rewriting.Rules.Rewrite as R
import qualified Data.Rewriting.Substitution.Type as S
import qualified Data.Map.Strict as Map
import Data.List (find)
import Data.Maybe (listToMaybe, isNothing)

-- | Represent a contraction with its terms, position, rule, and matched arguments.
data Step c v = Step (Term c v) (Term c v) Pos (Rule c)
  (Map.Map Int (Term c v))
  deriving (Eq, Show)

-- | Return the term before a contraction.
stepBefore :: Step c v -> Term c v
stepBefore (Step t _ _ _ _) = t

-- | Return the term after a contraction.
stepAfter :: Step c v -> Term c v
stepAfter (Step _ t _ _ _) = t

-- | Return the position of the contracted subtree.
stepPosition :: Step c v -> Pos
stepPosition (Step _ _ p _ _) = p

-- | Return the rule used for a contraction.
stepRule :: Step c v -> Rule c
stepRule (Step _ _ _ r _) = r

-- | Return the matched arguments indexed from one.
stepArguments :: Step c v -> Map.Map Int (Term c v)
stepArguments (Step _ _ _ _ args) = args

convert :: Eq c => Basis c -> Term c v -> R.Reduct (Symbol c) v Int -> Step c v
convert b before r = case find ((== R.rule r) . toRewriteRule) (basisRules b) of
  Nothing -> error "Combinator.Reduction: engine returned an unregistered rule"
  Just spec -> Step before (Term (R.result r)) (R.pos r) spec
    (Map.map Term (S.toMap (R.subst r)))

-- | Return the leftmost-innermost contraction, or 'Nothing' when no redex exists.
stepLI :: (Eq c, Eq v) => Basis c -> Term c v -> Maybe (Step c v)
stepLI b t = convert b t <$> listToMaybe
  (R.innerRewrite (map toRewriteRule (basisRules b)) (unTerm t))

-- | List all one-step weak contractions in preorder of their positions.
weakSteps :: (Eq c, Eq v) => Basis c -> Term c v -> [Step c v]
weakSteps b t = map (convert b t)
  (R.fullRewrite (map toRewriteRule (basisRules b)) (unTerm t))

-- | Contract a redex at the given position, or return 'Nothing' if none exists.
contractAt :: (Eq c, Eq v) => Basis c -> Term c v -> Pos -> Maybe (Step c v)
contractAt b t p = find ((== p) . stepPosition) (weakSteps b t)

-- | Check whether a term contains no redex for the given basis.
isNormal :: (Eq c, Eq v) => Basis c -> Term c v -> Bool
isNormal b = isNothing . stepLI b
