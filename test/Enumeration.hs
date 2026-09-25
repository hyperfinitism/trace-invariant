{-# LANGUAGE BangPatterns #-}
module Enumeration
  ( termsWithLeaves, termsUpToLeaves, rightmostCondition
  , SmallFailure(..), SmallReport(..), checkSmallBMI
  ) where

import Combinator.Term
import Combinator.Rule
import Combinator.Reduction
import Combinator.Trace
import qualified Data.Set as Set
import Numeric.Natural (Natural)

termsWithLeaves :: (Ord c, Ord v) => Int -> [c] -> [v] -> [Term c v]
termsWithLeaves n cs vs
  | n <= 0 = []
  | otherwise = table !! n
  where
    atoms = map constant (Set.toAscList (Set.fromList cs))
         ++ map var (Set.toAscList (Set.fromList vs))
    table = [] : atoms :
      [ [a @@ b | k <- [1..m-1], a <- table !! k, b <- table !! (m-k)]
      | m <- [2..n] ]

termsUpToLeaves :: (Ord c, Ord v) => Int -> [c] -> [v] -> [Term c v]
termsUpToLeaves n cs vs = concat [termsWithLeaves k cs vs | k <- [1..n]]

rightmostCondition :: (Eq c, Eq v) => Basis c -> v -> Term c v -> Bool
rightmostCondition basis x t = case view t of
  Variable v -> v == x
  Combinator _ -> False
  Apply a b -> isNormal basis a && rightmostCondition basis x b

data SmallFailure = SmallFailure
  { failureInitialP :: Term String String
  , failureStep :: Natural
  , failureExplanation :: String
  } deriving (Eq, Show)

data SmallReport = SmallReport
  { smallCandidateCount :: Natural
  , smallEligibleCount :: Natural
  , smallDiscardedCount :: Natural
  , smallStatesChecked :: Natural
  , smallMEvents :: Natural
  , smallConsecutivePairs :: Natural
  , smallNormalRuns :: Natural
  , smallStepLimitedRuns :: Natural
  , smallNodeLimitedRuns :: Natural
  , smallFailures :: [SmallFailure]
  } deriving (Eq, Show)

emptyReport :: SmallReport
emptyReport = SmallReport 0 0 0 0 0 0 0 0 0 []

combine :: SmallReport -> SmallReport -> SmallReport
combine a b = SmallReport
  (smallCandidateCount a + smallCandidateCount b)
  (smallEligibleCount a + smallEligibleCount b)
  (smallDiscardedCount a + smallDiscardedCount b)
  (smallStatesChecked a + smallStatesChecked b)
  (smallMEvents a + smallMEvents b)
  (smallConsecutivePairs a + smallConsecutivePairs b)
  (smallNormalRuns a + smallNormalRuns b)
  (smallStepLimitedRuns a + smallStepLimitedRuns b)
  (smallNodeLimitedRuns a + smallNodeLimitedRuns b)
  (smallFailures a ++ smallFailures b)

checkSmallBMI :: Int -> Natural -> Natural -> SmallReport
checkSmallBMI leaves stepBudget nodeBudget = foldl' combine emptyReport
  (map checkOne (termsUpToLeaves leaves ["B","M","I"] []))
  where
    checkOne p
      | not (isNormal basisBMI p) = emptyReport
          { smallCandidateCount = 1, smallDiscardedCount = 1 }
      | otherwise = walk p 0 Nothing (p @@ var "x")
          (emptyReport { smallCandidateCount = 1, smallEligibleCount = 1 })
    failAt p index message report = report
      { smallFailures = [SmallFailure p index message] }
    walk p !index previousQ term !report
      | exceedsNodes nodeBudget term = report { smallNodeLimitedRuns = 1 }
      | not (rightmostCondition basisBMI "x" term) =
          failAt p index "Rightmost-leaf structural condition failed" report
      | otherwise =
          let checked = report { smallStatesChecked = smallStatesChecked report + 1 }
          in case stepLI basisBMI term of
            Nothing -> checked { smallNormalRuns = 1 }
            Just st
              | index >= stepBudget -> checked { smallStepLimitedRuns = 1 }
              | exceedsNodes nodeBudget (stepAfter st) -> checked { smallNodeLimitedRuns = 1 }
              | otherwise -> case observeStep mObserver "x" index st of
                  Left e -> failAt p index (show e) checked
                  Right [] -> walk p (index+1) previousQ (stepAfter st) checked
                  Right [event] ->
                    let q = eventQ event
                        counted = checked
                          { smallMEvents = smallMEvents checked + 1
                          , smallConsecutivePairs = smallConsecutivePairs checked
                              + maybe 0 (const 1) previousQ }
                    in if maybe False (q <=) previousQ
                         then failAt p index "Consecutive M coordinates did not strictly increase" counted
                         else walk p (index+1) (Just q) (stepAfter st) counted
                  Right _ -> failAt p index "Unexpected multiple M observations" checked
