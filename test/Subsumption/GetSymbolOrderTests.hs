{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.GetSymbolOrderTests (runGetSymbolOrderTests) where


import FOL (Clause(..), Literal(..), Predicate(..), Term(..))
import Subsumption.SubsumptionFilter (getSymbolOrder)
import Data.List (sort)

pP = "_P_P"
pQ = "_P_Q"
fA = "_F_a"
fB = "_F_b"
fF = "_F_f"
notPP = "_¬__P_P"


clauses1 = []
expectedSO1 = []

clauses2 = [Clause [Pos (R ("P", [Fn ("a", [])]))]]
expectedSO2 = sort [pP, fA]

clauses3 = 
    [ Clause [Pos (R ("P", [Fn ("a", [])]))]
    , Clause [Pos (R ("Q", [Fn ("b", [])]))]
    ]
expectedSO3 = sort [pP, pQ, fA, fB]

clauses4 = 
    [ Clause [Pos (R ("P", [Fn ("a", [])]))]
    , Clause [Neg (R ("P", [Fn ("a", [])]))]
    ]
expectedSO4 = sort [pP, notPP, fA]

clauses5 = 
    [ Clause [Pos (R ("P", [Fn ("f", [Fn ("a", [])])]))]
    , Clause [Pos (R ("P", [Fn ("f", [Fn ("b", [])])]))]
    ]
expectedSO5 = sort [pP, fF, fA, fB]


-- Verification logic
testSO1 = getSymbolOrder clauses1 == expectedSO1
testSO2 = getSymbolOrder clauses2 == expectedSO2
testSO3 = getSymbolOrder clauses3 == expectedSO3
testSO4 = getSymbolOrder clauses4 == expectedSO4
testSO5 = getSymbolOrder clauses5 == expectedSO5

runGetSymbolOrderTests = concat
    [
        "\n\n Running Get Symbol Order Tests", 
        "\n Test 1: " ++ show testSO1,
        "\n Test 2: " ++ show testSO2,
        "\n Test 3: " ++ show testSO3,
        "\n Test 4: " ++ show testSO4,
        "\n Test 5: " ++ show testSO5
    ]