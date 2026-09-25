module Reference (RefTerm(..), RefStep(..), toRef, fromRef, refLI) where

import Combinator.Term
import Data.Maybe (isJust)

data RefTerm = RVar String | RCon String | RApp RefTerm RefTerm
  deriving (Eq, Ord, Show)

data RefStep = RefStep
  { refAfter :: RefTerm
  , refPosition :: [Int]
  , refRule :: String
  , refArguments :: [RefTerm]
  } deriving (Eq, Show)

toRef :: Term String String -> RefTerm
toRef = foldTerm RVar RCon RApp

fromRef :: RefTerm -> Term String String
fromRef (RVar x) = var x
fromRef (RCon c) = constant c
fromRef (RApp a b) = fromRef a @@ fromRef b

refLI :: [String] -> RefTerm -> Maybe RefStep
refLI basis (RApp a b)
  | isJust left = fmap (\st -> st { refAfter = RApp (refAfter st) b
                                , refPosition = 0 : refPosition st }) left
  | isJust right = fmap (\st -> st { refAfter = RApp a (refAfter st)
                                 , refPosition = 1 : refPosition st }) right
  | otherwise = root basis (RApp a b)
  where
    left = refLI basis a
    right = refLI basis b
refLI _ _ = Nothing

root :: [String] -> RefTerm -> Maybe RefStep
root basis term = do
  let (headTerm, args) = decompose term []
  name <- case headTerm of
    RCon c | c `elem` basis -> Just c
    _ -> Nothing
  after <- case (name,args) of
    ("B",[a,b,c]) -> Just (RApp a (RApp b c))
    ("C",[a,b,c]) -> Just (RApp (RApp a c) b)
    ("I",[a]) -> Just a
    ("M",[a]) -> Just (RApp a a)
    ("W",[a,b]) -> Just (RApp (RApp a b) b)
    ("S",[a,b,c]) -> Just (RApp (RApp a c) (RApp b c))
    _ -> Nothing
  pure (RefStep after [] name args)
  where
    decompose (RApp a b) args = decompose a (b:args)
    decompose a args = (a,args)
