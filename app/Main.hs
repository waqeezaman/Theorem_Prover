{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use ++" #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Main where

import Options.Applicative
    ( (<**>),
      optional,
      footer,
      fullDesc,
      header,
      help,
      info,
      long,
      metavar,
      prefs,
      progDesc,
      short,
      showHelpOnEmpty,
      showHelpOnError,
      strArgument,
      strOption,
      customExecParser,
      helper,
      Parser )
import Parser (parseTPTP)
import Text.Megaparsec (errorBundlePretty)
import FOL ( Clause(Clause) )
import HandleProof ( writeProofToFile )
import Control.Monad.State ( evalState )
import Config (loadConfig, defaultConfig, Config(..))
import PassiveQueue ( pqConfigToPQ )
import Filtering ( composeFilteringTypesIntoFilterFunction )
import GivenClauseLoop.State
    ( ProofSearch(_isUnsat, _derivation), initialiseState )
import GivenClauseLoop.Solver ( solve )


data ProverMode = WriteProof | NSteps | ProofSearch | Solver | SubsumptionProof | SubsumptionSolve

data Options = Options
    {
        input :: FilePath,
        output :: Maybe FilePath,
        config :: Maybe FilePath
    }


optionsParser :: Parser Options
optionsParser = Options
    <$> strArgument (metavar "INPUT" <> help "TPTP input file")
    <*> optional (strOption (long "output" <> short 'o' <> metavar "FILE" <> help "Output file path"))
    <*> optional (strOption (long "config" <> short 'c' <> metavar "CONFIG" <> help "Config file path"))

main :: IO ()
main = do
    let p = prefs (showHelpOnEmpty <> showHelpOnError)
    let m = info (optionsParser <**> helper)
            (  fullDesc
            <> progDesc "A First Order Logic Resolution Prover"
            <> header "Theorem-Prover"
            <> footer "Example: Theorem-Prover solve PUZ001-1.p"
            )
    opts <- customExecParser p m
    runWithOptions opts


runWithOptions :: Options -> IO ()
runWithOptions opts = runProver opts.input opts.output opts.config

runProver :: FilePath -> Maybe FilePath -> Maybe FilePath -> IO ()
runProver inputFile mOutputFile mConfigFile = do
    contents <- readFile inputFile
    case parseTPTP contents of
        Left parseError -> do
            putStrLn "Parser Error"
            putStrLn (errorBundlePretty parseError)
        Right clauses -> do
            let axioms = map Clause clauses
            
            config <- case mConfigFile of
                        Just path -> loadConfig path
                        Nothing   -> return defaultConfig

            let passiveQueues = map pqConfigToPQ config.passiveQueues
            let filterFunction = composeFilteringTypesIntoFilterFunction config.filterFunction
            let initialState = initialiseState axioms config.stopAfterNSteps passiveQueues filterFunction
            
            let proof = evalState solve initialState

            case mOutputFile of
                Just path -> writeProofToFile path proof._derivation
                Nothing   -> putStrLn "No output file specified; skipping file save."

            print proof._isUnsat
