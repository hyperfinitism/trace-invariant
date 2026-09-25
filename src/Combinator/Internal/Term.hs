module Combinator.Internal.Term (Symbol(..), Term(..)) where

import qualified Data.Rewriting.Term.Type as R

data Symbol c = Application | Constant c
  deriving (Eq, Ord, Show)

newtype Term c v = Term { unTerm :: R.Term (Symbol c) v }
  deriving (Eq, Ord, Show)
