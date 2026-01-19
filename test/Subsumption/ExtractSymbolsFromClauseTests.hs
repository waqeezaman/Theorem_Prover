{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.ExtractSymbolsFromClauseTests (runExtractSymbolsFromClauseTests) where


import FOL (Clause(..), Literal(..), Predicate(..), Term(..))
import Subsumption.SubsumptionFilter ( extractSymbolsFromClause )
import Data.List (sort)


clause1 = Clause []
expectedC1 = []

clause2 = Clause [Pos (R ("P", [Fn ("f", [Var "X"])]))]
expectedC2 = ["_P_P", "_F_f"]

clause3 = Clause 
    [ Pos (R ("P", [Fn ("a", [])]))
    , Neg (R ("Q", [Fn ("b", [])]))
    ]
expectedC3 = ["_P_P", "_F_a", "_¬__P_Q", "_F_b"]

clause4 = Clause 
    [ Pos (R ("P", [Fn ("a", [])]))
    , Pos (R ("P", [Fn ("a", [])]))
    ]
expectedC4 = ["_P_P", "_F_a",  "_P_P", "_F_a"]

clause5 = Clause 
    [ Neg (R ("P", [Fn ("a", [])]))
    , Neg (R ("Q", [Fn ("a", [])]))
    ]
expectedC5 = ["_¬__P_P", "_F_a",  "_¬__P_Q", "_F_a"]

-- Verification logic
test1 = sort (extractSymbolsFromClause clause1) == sort expectedC1
test2 = sort (extractSymbolsFromClause clause2) == sort expectedC2
test3 = sort (extractSymbolsFromClause clause3) == sort expectedC3
test4 = sort (extractSymbolsFromClause clause4) == sort expectedC4
test5 = sort (extractSymbolsFromClause clause5) == sort expectedC5


runExtractSymbolsFromClauseTests = concat
    [
        "\n\n Running Clause Symbol Extraction Tests", 
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5
    ]