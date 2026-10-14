{-# LANGUAGE OverloadedStrings #-}
module Output
  ( pointValue, eventValue, runValue, analysisValue, stopName ) where

import Combinator
import Data.Aeson (Value, object, toJSON, (.=))
import qualified Data.List.NonEmpty as NE

pointValue :: TracePoint -> Value
pointValue p = toJSON [toInteger (traceP p), toInteger (traceQ p)]

eventValue :: Event String -> Value
eventValue e = object
  [ "step" .= toInteger (eventStep e)
  , "rule" .= eventRule e
  , "argument" .= eventArgument e
  , "multiplicity" .= toInteger (eventMultiplicity e)
  , "position" .= eventPosition e
  , "p" .= toInteger (eventP e)
  , "q" .= toInteger (eventQ e)
  ]

stopName :: StopReason c -> String
stopName NormalForm = "normal-form"
stopName StepBudgetReached = "step-budget"
stopName EventBudgetReached = "event-budget"
stopName NodeBudgetReached = "node-budget"
stopName (RepeatedState _) = "cycle"

cycleValue :: Cycle String -> Value
cycleValue c = object
  [ "startStep" .= toInteger (cycleStartStep c)
  , "endStep" .= toInteger (cycleEndStep c)
  , "startEvent" .= toInteger (cycleStartEvent c)
  , "eventBlock" .= map eventValue (cycleEventBlock c)
  , "observerHasInfiniteEvents" .= not (null (cycleEventBlock c))
  ]

runValue :: RunResult String String -> Value
runValue r = object
  [ "strategy" .= ("leftmost-innermost" :: String)
  , "steps" .= toInteger (resultSteps r)
  , "stop" .= stopName (resultStop r)
  , "events" .= map eventValue (resultEvents r)
  , "points" .= map pointValue (resultPoints r)
  , "residual" .= renderNamedTerm (resultTerm r)
  , "residualNodes" .= toInteger (nodeCount (resultTerm r))
  , "cycle" .= case resultStop r of
      RepeatedState c -> Just (cycleValue c)
      _ -> Nothing
  ]

analysisValue :: Analysis String -> Value
analysisValue (Unresolved r) = object
  [ "status" .= ("unresolved" :: String)
  , "run" .= runValue r
  ]
analysisValue (Resolved inv) = object
  [ "status" .= ("resolved" :: String)
  , "theory" .= show (invariantTheory inv)
  , "variable" .= invariantVariable inv
  , "value" .= case viewInvariant inv of
      NormalInvariant t -> object
        [ "kind" .= ("normal-form" :: String), "term" .= renderNamedTerm t ]
      PeriodicInvariant trace -> object
        [ "kind" .= ("periodic-tail-class" :: String)
        , "canonicalPeriod" .= map pointValue (NE.toList (periodBlock trace)) ]
  ]
