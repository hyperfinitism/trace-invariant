{-# LANGUAGE OverloadedStrings #-}
module Config (loadExtraRules) where

import Control.Monad
import Combinator
import Data.Aeson (FromJSON(..), withObject, (.:), eitherDecodeStrict')
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import System.IO.Error (tryIOError)

data Definition = Definition String [String] String
newtype Configuration = Configuration [Definition]

instance FromJSON Definition where
  parseJSON = withObject "rule definition" $ \o ->
    Definition <$> o .: "symbol" <*> o .: "arguments" <*> o .: "rhs"

instance FromJSON Configuration where
  parseJSON = withObject "rule configuration" $ \o -> Configuration <$> o .: "rules"

compileDefinition :: Definition -> Either String (Rule String)
compileDefinition (Definition name arguments rhsText) = do
  let names = Map.fromList (zip arguments [1..])
  Control.Monad.when (Map.size names /= length arguments)
    $ Left ("Rule " ++ name ++ ": duplicate argument names")
  parsed <- parseTerm rhsText
  body <- foldTerm
    (\v -> maybe (Left ("Rule " ++ name ++ ": undeclared argument " ++ show v))
                  (Right . var) (Map.lookup v names))
    (Right . constant)
    (liftA2 (@@)) parsed
  either (Left . (("Rule " ++ name ++ ": ") ++) . show) Right
    (mkRule name (length arguments) body)

loadExtraRules :: FilePath -> IO (Either String [Rule String])
loadExtraRules path = do
  readResult <- tryIOError (BS.readFile path)
  pure $ do
    bytes <- either (Left . show) Right readResult
    Configuration definitions <- eitherDecodeStrict' bytes
    traverse compileDefinition definitions
