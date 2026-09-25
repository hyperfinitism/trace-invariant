module Combinator.Invariant
  ( Theory(..), theoryBasis, theoryObserver
  , Invariant, InvariantView(..), invariantTheory, invariantVariable, viewInvariant
  , Analysis(..), InvariantError(..), analyseInvariant, analyseBMI, analyseBWI
  , equalInvariants, starInvariant
  ) where

import Combinator.Term
import Combinator.Rule
import Combinator.Trace
import Combinator.Trace.Periodic
import qualified Data.List.NonEmpty as NE

-- | Select the BMI or BWI invariant theory.
data Theory = BMI | BWI deriving (Eq, Ord, Show, Read)

-- | Return the reduction basis for an invariant theory.
theoryBasis :: Theory -> Basis String
theoryBasis BMI = basisBMI
theoryBasis BWI = basisBWI

-- | Return the M observer for BMI or the W observer for BWI.
theoryObserver :: Theory -> Observer String
theoryObserver BMI = mObserver
theoryObserver BWI = wObserver

-- | Expose an invariant as a normal term or a periodic trace tail class.
data InvariantView v
  = NormalInvariant (Term String v)
  | PeriodicInvariant PeriodicTrace
  deriving (Eq, Show)

-- | Represent a resolved invariant with its theory and target variable.
data Invariant v = Invariant Theory v (InvariantView v)
  deriving Show

-- | Return the theory associated with an invariant.
invariantTheory :: Invariant v -> Theory
invariantTheory (Invariant theory _ _) = theory

-- | Return the variable tracked by an invariant.
invariantVariable :: Invariant v -> v
invariantVariable (Invariant _ v _) = v

-- | Return the normal term or periodic tail class represented by an invariant.
viewInvariant :: Invariant v -> InvariantView v
viewInvariant (Invariant _ _ value) = value

-- | Return a resolved invariant or an unresolved run with its stopping reason.
data Analysis v
  = Resolved (Invariant v)
  | Unresolved (RunResult String v)
  deriving Show

-- | Report invalid inputs or incompatible invariant theories or target variables.
data InvariantError
  = InvariantRunError (RunError String)
  | DifferentTheories
  | DifferentTargetVariables
  deriving (Eq, Show)

-- | Return a normal form or a periodic trace representative from a repeated LI state, within the supplied limits.
analyseInvariant :: Ord v => Theory -> v -> Limits -> Term String v
  -> Either InvariantError (Analysis v)
analyseInvariant theory x limits term = do
  r <- either (Left . InvariantRunError) Right
    (runTrace (theoryBasis theory) (theoryObserver theory) x
      (limits { detectCycles = True }) term)
  pure $ case resultStop r of
    NormalForm -> Resolved (Invariant theory x (NormalInvariant (resultTerm r)))
    RepeatedState c -> case NE.nonEmpty (map eventPoint (cycleEventBlock c)) of
      Just block -> Resolved (Invariant theory x (PeriodicInvariant (periodicClass block)))
      Nothing -> Unresolved r
    _ -> Unresolved r

-- | Compute the BMI invariant of a term within the supplied limits.
analyseBMI :: Ord v => v -> Limits -> Term String v
  -> Either InvariantError (Analysis v)
analyseBMI = analyseInvariant BMI
-- | Compute the BWI invariant of a term within the supplied limits.
analyseBWI :: Ord v => v -> Limits -> Term String v
  -> Either InvariantError (Analysis v)
analyseBWI = analyseInvariant BWI

compatible :: Eq v => Invariant v -> Invariant v -> Either InvariantError ()
compatible a b
  | invariantTheory a /= invariantTheory b = Left DifferentTheories
  | invariantVariable a /= invariantVariable b = Left DifferentTargetVariables
  | otherwise = Right ()

-- | Compare resolved invariants exactly, requiring matching theories and target variables.
equalInvariants :: Eq v => Invariant v -> Invariant v -> Either InvariantError Bool
equalInvariants a b = compatible a b >> pure (viewInvariant a == viewInvariant b)

-- | Apply the paper's partial algebra operation, using bounded analysis for two normal terms.
starInvariant :: Ord v => Limits -> Invariant v -> Invariant v
  -> Either InvariantError (Analysis v)
starInvariant limits a b = do
  compatible a b
  case (viewInvariant a, viewInvariant b) of
    (PeriodicInvariant _, _) -> pure (Resolved a)
    (NormalInvariant u, PeriodicInvariant trace) -> pure (Resolved
      (Invariant (invariantTheory a) (invariantVariable a)
        (PeriodicInvariant (shiftPeriodic (occurrences (invariantVariable a) u) trace))))
    (NormalInvariant u, NormalInvariant v) ->
      analyseInvariant (invariantTheory a) (invariantVariable a) limits (u @@ v)
