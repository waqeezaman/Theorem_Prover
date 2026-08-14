{-# HLINT ignore "Use ++" #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

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
import Control.Lens ( (^.) )
import FOL ( Clause(Clause) )
import HandleProof ( writeProofToFile )
import GivenClauseLoop.State
    ( ProofSearch(_derivation), isUnsat )
import Config
    ( defaultProofSearchConfig, loadProofSearchConfig )
import Scheduler (runSchedule)

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
runProver inputFile outputFile configFile = do
    contents <- readFile inputFile
    case parseTPTP contents of
        Left parseError -> do
            putStrLn "Parser Error"
            print (errorBundlePretty parseError)
        Right clauses -> do
            let axioms = map Clause clauses
            config <- case configFile of
                        Just path -> loadProofSearchConfig path
                        Nothing   -> return defaultProofSearchConfig
            proofSearchOutput <- runSchedule config axioms

            case proofSearchOutput of
                Nothing -> putStrLn "No proof found within constraints"
                Just proof -> do
                    case outputFile of
                        Just path -> writeProofToFile path proof._derivation
                        Nothing   -> putStrLn "No output file specified; skipping file save."
                    case proof ^. isUnsat of
                        Nothing -> putStrLn "No proof found within constraints"
                        Just x -> print x
