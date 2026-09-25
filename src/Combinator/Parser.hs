module Combinator.Parser (parseTerm, termParser) where

import Combinator.Term
import Control.Applicative (empty, (<|>), many)
import Data.Bifunctor (first)
import Data.Char (isAsciiUpper, isAsciiLower)
import Data.Void (Void)
import Text.Megaparsec
  ( Parsec, eof, runParser, errorBundlePretty, between, satisfy, anySingle )
import Text.Megaparsec.Char (char, space1)
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

-- | Parse left-associative applications with letter atoms, @[constant]@ names, and @{variable}@ names.
termParser :: Parser (Term String String)
termParser = do
  firstTerm <- atom
  rest <- many atom
  pure (apps firstTerm rest)
  where
    atom :: Parser (Term String String)
    atom = lexeme $
      between (lexeme (char '(')) (char ')') termParser
      <|> (constant . (:[]) <$> satisfy isAsciiUpper)
      <|> (var . (:[]) <$> satisfy isAsciiLower)
      <|> (constant <$> named '[' ']')
      <|> (var <$> named '{' '}')
    named :: Char -> Char -> Parser String
    named open close = between (char open) (char close)
      (many ((char '\\' *> anySingle)
        <|> satisfy (\c -> c /= close && c /= '\\')))

-- | Parse a complete term, returning an error with source position on failure.
parseTerm :: String -> Either String (Term String String)
parseTerm = first errorBundlePretty . runParser (sc *> termParser <* eof) "<term>"
