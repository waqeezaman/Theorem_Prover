{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use ++" #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Main where

import System.Environment (getArgs)
import qualified Data.ByteString.Lazy.Char8 as ByteString
import Data.Aeson.Encode.Pretty (encodePretty)
import Parser (parseTPTP)
import GivenClauseLoop (solve, findDerivedClausesForNSteps, findAllDerivedClauses, proofSearchAfterNSteps, resolution, DerivedClause(..), solveWithResult, ProofResult (isUnsat))
import Text.Megaparsec (errorBundlePretty)
import FOL
import Unification (standardiseApartClause, unifyingPairs, applySubToClause, applySubToLiteral)
import Resolution
import Utils
import Data.List (sortOn)
import Factoring (factorise)

main = do
    args <- getArgs
    case args of
        [inputFile] -> runProver inputFile
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
            -- let initialPassives = map (\c -> Derived { derived = Clause c, parent1 = Clause [], parent2 = Clause []}) clauses
            let result = solve clauses --solveWithResult initialPassives []
            -- let result = solveWithResult initialPassives []

            -- let proof = proofSearchAfterNSteps (map (\c -> (c, [], [])) clauses) [] 2

            print result
            -- mapM_ print proof
            -- print (isUnsat result)
            -- let jsonOutput = encodePretty result

            -- ByteString.writeFile outputFile jsonOutput
            -- putStrLn $ "Proof result saved to: " ++ outputFile


