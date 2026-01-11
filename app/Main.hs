{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use ++" #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Main where

import System.Environment (getArgs)
import Parser (parseTPTP)
import GivenClauseLoop
import Text.Megaparsec (errorBundlePretty)
import FOL
import HandleProof (writeProofToFile)
import Control.Monad.State (evalState)

main = do
    args <- getArgs
    case args of
        [inputFile] -> runForNSteps inputFile
        [inputFile, outputFile] -> writeProof inputFile outputFile
        _ -> do
            putStrLn "Usage: cabal run Theorem-Prover -- <input.p>"


-- main :: IO ()
runProver inputFile = do
    input <- readFile inputFile

    case parseTPTP input of
        Left err -> do
            putStrLn "Parser Error:"
            putStrLn (errorBundlePretty err)

        Right clauses -> do
            let result = solve (map Clause clauses) 
            print result


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


runForNSteps inputFile = do 
    input <- readFile inputFile
    case parseTPTP input of
        Left err -> do
            putStrLn "Parser Error:"
            putStrLn (errorBundlePretty err)

        Right clauses -> do
            let axioms = createAxioms clauses
            let result = evalState (proofSearchAfterNSteps 3000 axioms [] ) (length axioms+1)
            print result
        
runAndPrintProofSearch inputFile = do 
    input <- readFile inputFile
    case parseTPTP input of
        Left err -> do
            putStrLn "Parser Error:"
            putStrLn (errorBundlePretty err)

        Right clauses -> do
            let axioms = createAxioms clauses
            let result = evalState (solveWithProofSearch axioms [] ) (length axioms+1)
            print result   