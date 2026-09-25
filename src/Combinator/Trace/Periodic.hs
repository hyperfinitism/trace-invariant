module Combinator.Trace.Periodic
  ( PeriodicTrace, periodicClass, periodBlock, periodicPrefix, shiftPeriodic ) where

import Combinator.Trace (TracePoint, shiftPoint)
import Combinator.Term (takeNatural)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe(fromMaybe)
import qualified Data.List.NonEmpty as NE
import Data.List (find)
import Numeric.Natural (Natural)

-- | Represent a periodic trace by its shortest, least cyclic rotation.
newtype PeriodicTrace = PeriodicTrace (NonEmpty TracePoint)
  deriving (Eq, Ord, Show)

-- | Canonicalise a nonempty repeating block up to cyclic rotation and period repetition.
periodicClass :: NonEmpty TracePoint -> PeriodicTrace
periodicClass input = PeriodicTrace canonical
  where
    xs = NE.toList input
    n = length xs
    candidates = [d | d <- [1..n], n `mod` d == 0]
    isPeriod d = take n (cycle (take d xs)) == xs
    d = Data.Maybe.fromMaybe n (find isPeriod candidates)
    shortest = take d xs
    rotations = [drop k shortest ++ take k shortest | k <- [0..d-1]]
    least = minimum rotations
    canonical = fromMaybe input (NE.nonEmpty least)

-- | Return the canonical period block of a periodic trace.
periodBlock :: PeriodicTrace -> NonEmpty TracePoint
periodBlock (PeriodicTrace block) = block

-- | Return a finite prefix of the canonical periodic representative.
periodicPrefix :: Natural -> PeriodicTrace -> [TracePoint]
periodicPrefix n = takeNatural n . cycle . NE.toList . periodBlock

-- | Add an offset to every second coordinate of a periodic trace.
shiftPeriodic :: Natural -> PeriodicTrace -> PeriodicTrace
shiftPeriodic n = periodicClass . fmap (shiftPoint n) . periodBlock
