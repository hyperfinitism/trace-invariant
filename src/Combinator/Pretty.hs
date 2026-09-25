module Combinator.Pretty (prettyTerm, renderTerm, renderNamedTerm, renderPosition) where

import Combinator.Term
import Prettyprinter (Doc, group, sep, parens, pretty, layoutPretty, defaultLayoutOptions)
import Prettyprinter.Render.String (renderString)
import Data.Char (isAsciiLower, isAsciiUpper)

-- | Build a precedence-aware document using the supplied constant and variable renderers.
prettyTerm :: (c -> Doc ann) -> (v -> Doc ann) -> Term c v -> Doc ann
prettyTerm showC showV = go False
  where
    go bracket t = case view t of
      Variable v -> showV v
      Combinator c -> showC c
      Apply a b ->
        let d = group (sep [go False a, go True b])
        in if bracket then parens d else d

-- | Render a term as text using the supplied constant and variable renderers.
renderTerm :: (c -> String) -> (v -> String) -> Term c v -> String
renderTerm showC showV = renderString . layoutPretty defaultLayoutOptions
  . prettyTerm (pretty . showC) (pretty . showV)

-- | Render a term with escaped names in syntax accepted by @parseTerm@.
renderNamedTerm :: Term String String -> String
renderNamedTerm = renderTerm showC showV
  where
    showC [c] | isAsciiUpper c = [c]
    showC s = '[' : escape ']' s ++ "]"
    showV [v] | isAsciiLower v = [v]
    showV s = '{' : escape '}' s ++ "}"
    escape close = concatMap (\c -> if c == close || c == '\\' then ['\\',c] else [c])

-- | Render a position as @root@ or an @L@/@R@ path, enclosing other indices in brackets.
renderPosition :: Pos -> String
renderPosition [] = "root"
renderPosition p = concatMap showDirection p
  where
    showDirection 0 = "L"
    showDirection 1 = "R"
    showDirection i = "[" ++ show i ++ "]"
