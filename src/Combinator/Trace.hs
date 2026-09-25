{-# LANGUAGE BangPatterns #-}
module Combinator.Trace
  ( TracePoint(..), shiftPoint, Event(..), eventPoint
  , Observer, allDuplicated, selectedArguments, mObserver, wObserver, sObserver
  , ObservationError(..), validateObserver, observeStep
  , Limits(..), defaultLimits, Cycle(..), StopReason(..), RunError(..)
  , traceStream, Checkpoint, RunResult, runTrace, resumeTrace
  , resultStop, resultTerm, resultSteps, resultEvents, resultPoints, checkpoint
  ) where

import Combinator.Term
import Combinator.Rule
import Combinator.Reduction
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Sequence as Seq
import Data.Foldable (toList)
import Numeric.Natural (Natural)

-- | Represent trace coordinates @(q,p)@: occurrences in the copied argument and before the redex.
data TracePoint = TracePoint { traceQ :: Natural, traceP :: Natural }
  deriving (Eq, Ord, Show)

-- | Add an offset to the second trace coordinate.
shiftPoint :: Natural -> TracePoint -> TracePoint
shiftPoint n (TracePoint q p) = TracePoint q (p+n)

-- | Record a copied argument's trace coordinates, rule, position, and zero-based step.
data Event c = Event
  { eventStep :: !Natural
  , eventRule :: !c
  , eventArgument :: !Int
  , eventMultiplicity :: !Natural
  , eventPosition :: !Pos
  , eventQ :: !Natural
  , eventP :: !Natural
  } deriving (Eq, Ord, Show)

-- | Return the trace coordinates of an event.
eventPoint :: Event c -> TracePoint
eventPoint e = TracePoint (eventQ e) (eventP e)

-- | Select which duplicated rule arguments contribute trace events.
data Observer c = AllDuplicated | Selected (Set.Set (c,Int))
  deriving (Eq, Ord, Show)

-- | Observe every duplicated argument of every rule.
allDuplicated :: Observer c
allDuplicated = AllDuplicated

-- | Select rule symbols and one-based argument indices, removing duplicate selections.
selectedArguments :: Ord c => [(c,Int)] -> Observer c
selectedArguments = Selected . Set.fromList

-- | Observe the first argument duplicated by M.
mObserver :: Observer String
mObserver = selectedArguments [("M",1)]
-- | Observe the second argument duplicated by W.
wObserver :: Observer String
wObserver = selectedArguments [("W",2)]
-- | Observe the third argument duplicated by S.
sObserver :: Observer String
sObserver = selectedArguments [("S",3)]

-- | Report invalid observer selections or missing contraction data.
data ObservationError c
  = UnknownObservedSymbol c
  | NotADuplicatedArgument c Int
  | MissingMatchedArgument c Int
  | InvalidRedexPosition Pos
  deriving (Eq, Show)

-- | Check that each selected argument is duplicated by a registered rule.
validateObserver :: Ord c => Basis c -> Observer c -> Either (ObservationError c) ()
validateObserver _ AllDuplicated = Right ()
validateObserver b (Selected selectors) = mapM_ check (Set.toList selectors)
  where
    check (c,i) = case lookupRule c b of
      Nothing -> Left (UnknownObservedSymbol c)
      Just r | argumentMultiplicity r i >= 2 -> Right ()
             | otherwise -> Left (NotADuplicatedArgument c i)

-- | Compute selected events in argument order, counting @p@ before the entire redex.
observeStep :: (Ord c, Eq v)
  => Observer c -> v -> Natural -> Step c v
  -> Either (ObservationError c) [Event c]
observeStep observer x index st = do
  p <- maybe (Left (InvalidRedexPosition (stepPosition st))) Right
    (prefixBefore x (stepBefore st) (stepPosition st))
  traverse (make p) selected
  where
    r = stepRule st
    c = ruleSymbol r
    selected = filter wanted (duplicatedArguments r)
    wanted (i,_) = case observer of
      AllDuplicated -> True
      Selected pairs -> Set.member (c,i) pairs
    make p (i,multiplicity) = do
      a <- maybe (Left (MissingMatchedArgument c i)) Right
        (Map.lookup i (stepArguments st))
      pure (Event index c i multiplicity (stepPosition st) (occurrences x a) p)

-- | Set optional cumulative step and event limits, a term-tree node bound, and cycle detection.
data Limits = Limits
  { maxSteps :: Maybe Natural
  , maxEvents :: Maybe Natural
  , maxNodes :: Maybe Natural
  , detectCycles :: Bool
  } deriving (Eq, Show)

-- | Request 20 events with a 10000-step limit, no node limit, and cycle detection disabled.
defaultLimits :: Limits
defaultLimits = Limits
  { maxSteps = Just 10000, maxEvents = Just 20
  , maxNodes = Nothing, detectCycles = False }

-- | Record a repeated complete term and the events from one traversal of its cycle.
data Cycle c = Cycle
  { cycleStartStep :: Natural
  , cycleEndStep :: Natural
  , cycleStartEvent :: Natural
  , cycleEventBlock :: [Event c]
  } deriving (Eq, Show)

-- | Describe normalisation, a resource limit, or a detected cycle.
data StopReason c
  = NormalForm
  | StepBudgetReached
  | EventBudgetReached
  | NodeBudgetReached
  | RepeatedState (Cycle c)
  deriving (Eq, Show)

-- | Report a term or observer that is invalid for the selected basis.
data RunError c
  = InvalidBasisTerm (BasisError c)
  | InvalidObserver (ObservationError c)
  deriving (Eq, Show)

-- | Lazily compute selected LI trace events, ending the list when reduction reaches a normal form.
traceStream :: (Ord c, Eq v)
  => Basis c -> Observer c -> v -> Term c v -> Either (RunError c) [Event c]
traceStream b observer x t = do
  either (Left . InvalidBasisTerm) Right (validateTerm b t)
  either (Left . InvalidObserver) Right (validateObserver b observer)
  pure (go 0 t)
  where
    go !index term = case stepLI b term of
      Nothing -> []
      Just st -> case observeStep observer x index st of
        Left _ -> error "Combinator.Trace: validated observer/step invariant violated"
        Right events -> events ++ go (index+1) (stepAfter st)

-- | Retain the reduction state, basis, observer, and target variable for resumption.
-- Accumulators are strict so deferred updates cannot retain older checkpoints.
data Checkpoint c v = Checkpoint
  { cpBasis :: Basis c
  , cpObserver :: Observer c
  , cpVariable :: v
  , cpTerm :: Term c v
  , cpSteps :: !Natural
  , cpEvents :: !(Seq.Seq (Event c))
  , cpEventCount :: !Natural
  , cpSeen :: !(Map.Map (Term c v) (Natural, Int))
  } deriving Show

-- | Pair a stopped trace computation with its resumable state.
data RunResult c v = RunResult (StopReason c) (Checkpoint c v)
  deriving Show

-- | Return the reason a trace computation stopped.
resultStop :: RunResult c v -> StopReason c
resultStop (RunResult reason _) = reason

-- | Return the resumable state of a stopped trace computation.
checkpoint :: RunResult c v -> Checkpoint c v
checkpoint (RunResult _ state) = state

-- | Return the residual term of a trace computation.
resultTerm :: RunResult c v -> Term c v
resultTerm = cpTerm . checkpoint

-- | Return the cumulative number of completed contractions.
resultSteps :: RunResult c v -> Natural
resultSteps = cpSteps . checkpoint

-- | Return recorded trace events in execution order.
resultEvents :: RunResult c v -> [Event c]
resultEvents = toList . cpEvents . checkpoint

-- | Return recorded trace coordinates in execution order.
resultPoints :: RunResult c v -> [TracePoint]
resultPoints = map eventPoint . resultEvents

-- | Record an LI trace up to normal form or the supplied limits, preserving complete event groups.
runTrace :: (Ord c, Ord v)
  => Basis c -> Observer c -> v -> Limits -> Term c v
  -> Either (RunError c) (RunResult c v)
runTrace b observer x limits t = do
  either (Left . InvalidBasisTerm) Right (validateTerm b t)
  either (Left . InvalidObserver) Right (validateObserver b observer)
  pure (resumeTrace limits (Checkpoint b observer x t 0 Seq.empty 0 Map.empty))

-- | Continue a checkpoint with cumulative budgets, preserving recorded steps and events.
resumeTrace :: (Ord c, Ord v) => Limits -> Checkpoint c v -> RunResult c v
resumeTrace limits initial = go cleaned
  where
    cleaned = if detectCycles limits then initial else initial { cpSeen = Map.empty }
    tooLarge t = maybe False (`exceedsNodes` t) (maxNodes limits)
    atEventLimit n = maybe False (n >=) (maxEvents limits)
    overEventLimit n = maybe False (n >) (maxEvents limits)
    stop = RunResult
    repeated state = if not (detectCycles limits) then Nothing else do
      (start, offset) <- Map.lookup (cpTerm state) (cpSeen state)
      if start < cpSteps state
        then Just (Cycle start (cpSteps state) (fromIntegral offset)
          (toList (Seq.drop offset (cpEvents state))))
        else Nothing
    go !state
      | tooLarge (cpTerm state) = stop NodeBudgetReached state
      | Just c <- repeated state = stop (RepeatedState c) state
      | otherwise = case stepLI (cpBasis state) (cpTerm state) of
          Nothing -> stop NormalForm state
          Just st
            | maybe False (cpSteps state >=) (maxSteps limits) -> stop StepBudgetReached state
            | atEventLimit (cpEventCount state) -> stop EventBudgetReached state
            | tooLarge (stepAfter st) -> stop NodeBudgetReached state
            | otherwise -> case observeStep (cpObserver state) (cpVariable state)
                                  (cpSteps state) st of
                Left _ -> error "Combinator.Trace: validated observer/step invariant violated"
                Right events
                  | overEventLimit (cpEventCount state + fromIntegral (length events)) ->
                      stop EventBudgetReached state
                  | otherwise ->
                      let seen = if detectCycles limits
                            then Map.insert (cpTerm state)
                                 (cpSteps state, Seq.length (cpEvents state)) (cpSeen state)
                            else Map.empty
                          next = state
                            { cpTerm = stepAfter st
                            , cpSteps = cpSteps state + 1
                            , cpEvents = cpEvents state Seq.>< Seq.fromList events
                            , cpEventCount = cpEventCount state + fromIntegral (length events)
                            , cpSeen = seen
                            }
                          forced = foldr seq () events
                      in forced `seq` go next
