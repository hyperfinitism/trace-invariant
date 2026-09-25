module Main (main) where

import Combinator
import Config (loadExtraRules)
import Output
import Control.Monad  
import Data.Aeson (Value, encode)
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.Foldable (toList)
import Options.Applicative
import Numeric.Natural (Natural)
import Text.Read (readMaybe)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import System.IO.Error (tryIOError)

data TermInput = InlineTerm String | TermFile FilePath

data Command
  = TraceCommand String (Maybe FilePath) String String Limits Bool TermInput
  | InvariantCommand Theory String Limits Bool TermInput

main :: IO ()
main = execParser options >>= execute
  where
    options = info (helper <*> commandParser)
      (fullDesc <> progDesc "Compute LI traces, normal forms, and periodic trace representatives")

commandParser :: Parser Command
commandParser = hsubparser
  ( command "trace" (info (helper <*> traceParser) (progDesc "Compute a prefix of the LI trace"))
 <> command "invariant" (info (helper <*> invariantParser)
      (progDesc "Compute a normal form or a periodic trace representative in BMI/BWI")) )

traceParser :: Parser Command
traceParser = TraceCommand
  <$> strOption (long "basis" <> value "BCIMW" <> showDefault <> metavar "BASIS"
      <> help "Built-in symbols, e.g. BMI, BWI, BCIMWS (or empty for custom-only)")
  <*> optional (strOption (long "rules" <> metavar "FILE" <> help "Additional non-erasing rules in JSON"))
  <*> strOption (long "track" <> value "all" <> showDefault <> metavar "SYMBOLS"
      <> help "all, or comma-separated rule names; track their duplicated arguments")
  <*> variableParser <*> limitsParser <*> jsonParser <*> termInputParser

invariantParser :: Parser Command
invariantParser = InvariantCommand
  <$> option (eitherReader readTheory)
      (long "theory" <> value BMI <> showDefault <> metavar "BMI|BWI"
        <> help "Basis and observer for the trace invariant")
  <*> variableParser <*> limitsParser <*> jsonParser <*> termInputParser
  where
    readTheory "BMI" = Right BMI
    readTheory "BWI" = Right BWI
    readTheory _ = Left "The theory must be BMI or BWI"

variableParser :: Parser String
variableParser = strOption
  (long "variable" <> value "x" <> showDefault <> metavar "NAME" <> help "Target object-language variable")

termInputParser :: Parser TermInput
termInputParser =
  (TermFile <$> strOption (long "term-file" <> metavar "FILE" <> help "Read a term from a text file"))
  <|> (InlineTerm <$> strArgument (metavar "TERM" <> help "Term to reduce"))

jsonParser :: Parser Bool
jsonParser = switch (long "json" <> help "Emit one versioned JSON value")

limitsParser :: Parser Limits
limitsParser = (Limits . Just
     <$>
       naturalOption
         "steps" 10000
         "Maximum total contractions, including unobserved steps")
  <*> (Just <$> naturalOption "events" 20 "Maximum recorded trace events")
  <*> optional (option (eitherReader readNatural)
      (long "nodes" <> metavar "N" <> help "Optional term-tree node limit"))
  <*> pure False

naturalOption :: String -> Natural -> String -> Parser Natural
naturalOption name def description = option (eitherReader readNatural)
  (long name <> value def <> showDefault <> metavar "N" <> help description)

readNatural :: String -> Either String Natural
readNatural s = case readMaybe s :: Maybe Integer of
  Just n | n >= 0 -> Right (fromInteger n)
  _ -> Left "Expected a non-negative integer"

fatal :: String -> IO a
fatal message = hPutStrLn stderr message >> exitFailure

require :: Show e => Either e a -> IO a
require = either (fatal . show) pure

requireText :: Either String a -> IO a
requireText = either fatal pure

loadTerm :: TermInput -> IO (Term String String)
loadTerm (InlineTerm termText) = requireText (parseTerm termText)
loadTerm (TermFile path) = do
  termText <- tryIOError (readFile path) >>= require
  requireText (parseTerm termText)

emitJSON :: Value -> IO ()
emitJSON = BL.putStrLn . encode

observerFromNames :: Basis String -> String -> Either String (Observer String)
observerFromNames _ "all" = Right allDuplicated
observerFromNames b text = selectedArguments . concat <$> traverse choose (splitComma text)
  where
    choose name = case lookupRule name b of
      Nothing -> Left ("Unknown observed rule: " ++ name)
      Just r -> case duplicatedArguments r of
        [] -> Left ("Rule has no duplicated arguments: " ++ name)
        args -> Right [(name,k) | (k,_) <- args]

splitComma :: String -> [String]
splitComma text = case break (== ',') text of
  (a,[]) -> [a]
  (a,_:rest) -> a : splitComma rest

execute :: Command -> IO ()
execute (TraceCommand basisName config track target limits json input) = do
  base <- requireText (namedBasis (map (:[]) (filter (/= ',') basisName)))
  extra <- maybe (pure []) (loadExtraRules >=> requireText) config
  basis <- require (extendBasis base extra)
  observer <- requireText (observerFromNames basis track)
  term <- loadTerm input
  result <- require (runTrace basis observer target limits term)
  if json then emitJSON (runValue result) else printRun result
execute (InvariantCommand theory target limits json input) = do
  term <- loadTerm input
  result <- require (analyseInvariant theory target limits term)
  if json then emitJSON (analysisValue result) else case result of
    Resolved inv -> do
      putStrLn ("Theory: " ++ show (invariantTheory inv))
      case viewInvariant inv of
        NormalInvariant t -> putStrLn ("Normal-form invariant: " ++ renderNamedTerm t)
        PeriodicInvariant p ->
          putStrLn ("Periodic trace representative (repeating block): "
            ++ show [(traceQ point, traceP point) | point <- toList (periodBlock p)])
    Unresolved run -> do
      putStrLn "Invariant unresolved within the supplied limits."
      printRun run

printRun :: RunResult String String -> IO ()
printRun r = do
  putStrLn ("Stop: " ++ stopName (resultStop r) ++ "; steps: " ++ show (resultSteps r))
  putStrLn "step  rule  argument  position  (q,p)"
  forM_ (resultEvents r) $ \e -> putStrLn
    (show (eventStep e) ++ "  " ++ eventRule e ++ "  " ++ show (eventArgument e)
      ++ "  " ++ renderPosition (eventPosition e)
      ++ "  " ++ show (eventQ e, eventP e))
  let label = case resultStop r of
        NormalForm -> "Normal form: "
        _ -> "Residual: "
  putStrLn (label ++ renderNamedTerm (resultTerm r))
