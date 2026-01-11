{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use ++" #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Main where

import Options.Applicative
import Parser (parseTPTP)
import GivenClauseLoop
    ( createAxioms,
      solve,
      solveWithProofSearch,
      solveWithProof,
      proofSearchAfterNSteps )
import Text.Megaparsec (errorBundlePretty)
import FOL
import HandleProof (writeProofToFile)
import Control.Monad.State (evalState)
import HandleProof (writeSearchToFile)

data ProverMode = WriteProof | NSteps | ProofSearch | Solver

data Options = Options
    {
        mode :: ProverMode,
        input :: FilePath,
        output :: Maybe FilePath,
        steps :: Int
    }

modeParser :: Parser ProverMode
modeParser = subparser
    (  command "write" (info (pure WriteProof) (progDesc "Solve and write proof to file"))
    <> command "nsteps" (info (pure NSteps) (progDesc "Run for N steps and print result"))
    <> command "search" (info (pure ProofSearch) (progDesc "Full proof search state printout"))
    <> command "solve"  (info (pure Solver) (progDesc "Standard solver (True/False only)"))
    )

optionsParser :: Parser Options
optionsParser = Options
    <$> (modeParser <|> pure Solver)
    <*> strArgument (metavar "INPUT" <> help "TPTP input file")
    <*> optional (strOption (long "output" <> short 'o' <> metavar "FILE" <> help "Output file path"))
    <*> option auto (long "steps" <> short 'n' <> value 3000 <> showDefault <> help "Max steps for search")



main :: IO ()
main = do
    let p = prefs (showHelpOnEmpty <> showHelpOnError)
    let m = info (optionsParser <**> helper)
            (  fullDesc
            <> progDesc "A First Order Logic Resolution Prover"
            <> header "Theorem-Prover v1.0 - Academic Logic Tool"
            <> footer "Example: Theorem-Prover PUZ001-1.p solve --verbose"
            )    
    opts <- customExecParser p m 
    runWithOptions opts


runWithOptions :: Options -> IO ()
runWithOptions (Options Solver f  _ _ )      = runProver f
runWithOptions (Options NSteps f (Just o) n )      = runForNSteps f o n
runWithOptions (Options NSteps _ Nothing _ ) = putStrLn "Error: --output required for proof search for n steps mode"
runWithOptions (Options WriteProof f  (Just o) _ ) = writeProof f o
runWithOptions (Options WriteProof _  Nothing _ )  = putStrLn "Error: --output required for write mode"
runWithOptions (Options ProofSearch f  (Just o) _ ) = runProofSearch f o
runWithOptions (Options ProofSearch _  Nothing _ ) = putStrLn "Error: --output required for proof search mode"

runProver inputFile = do
    input <- readFile inputFile

    case parseTPTP input of
        Left err -> do
            putStrLn "Parser Error:"
            putStrLn (errorBundlePretty err)

        Right clauses -> do
            let result = solve (map Clause clauses)
            print result


writeProof :: FilePath -> FilePath -> IO ()
writeProof inputFile outputFile = do
    input <- readFile inputFile
    case parseTPTP input of
        Left err -> do
            putStrLn "Parser Error:"
            putStrLn (errorBundlePretty err)

        Right clauses -> do
            let axioms = createAxioms clauses
            let result = evalState (solveWithProof axioms []) (length axioms+1)
            writeProofToFile outputFile result


runForNSteps :: FilePath -> FilePath -> Int -> IO ()
runForNSteps inputFile outputFile n = do
    input <- readFile inputFile
    case parseTPTP input of
        Left err -> do
            putStrLn "Parser Error:"
            putStrLn (errorBundlePretty err)

        Right clauses -> do
            let axioms = createAxioms clauses
            let result = evalState (proofSearchAfterNSteps n axioms [] ) (length axioms+1)
            writeSearchToFile outputFile result

runProofSearch :: FilePath -> FilePath -> IO ()
runProofSearch inputFile outputFile = do
    input <- readFile inputFile
    case parseTPTP input of
        Left err -> do
            putStrLn "Parser Error:"
            putStrLn (errorBundlePretty err)

        Right clauses -> do
            let axioms = createAxioms clauses
            let result = evalState (solveWithProofSearch axioms [] ) (length axioms+1)
            writeSearchToFile outputFile result