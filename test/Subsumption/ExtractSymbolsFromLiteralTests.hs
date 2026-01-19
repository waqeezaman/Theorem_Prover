{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.ExtractSymbolsFromLiteralTests where



import FOL (Literal(..), Predicate(..), Term(..))
import Subsumption.SubsumptionFilter (extractSymbolsFromLiteral)
import Data.List (sort)

-- Test 1: Simple Positive Propositional Literal (No terms)
lit1 = Pos (R ("P", []))
expectedL1 = ["_P_P"]

-- Test 2: Negative Literal with Constants and Variables
-- ¬Q(a, X) -> Symbols: Q, a
lit2 = Neg (R ("Q", [Fn ("a", []), Var "X"]))
expectedL2 = ["_¬__P_Q", "_F_a"]

-- Test 3: Deeply Nested Function Symbols in a Literal
-- P(f(g(b))) -> Symbols: P, f, g, b
lit3 = Pos (R ("P", [Fn ("f", [Fn ("g", [Fn ("b", [])])])]))
expectedL3 = ["_P_P", "_F_f", "_F_g", "_F_b"]

-- Test 4: Multiple terms with shared symbols
-- P(f(a), f(b)) -> Symbols: P, f, a, f, b
lit4 = Pos (R ("P", [Fn ("f", [Fn ("a", [])]), Fn ("f", [Fn ("b", [])])]))
expectedL4 = ["_P_P", "_F_f", "_F_a", "_F_f", "_F_b"]

lit5 = Neg (R ("P", [Fn ("f", [Fn ("a", [])]), Fn ("f", [Fn ("b", [])])]))
expectedL5 = ["_¬__P_P", "_F_f", "_F_a", "_F_f", "_F_b"]


-- Verification logic
test1 = sort (extractSymbolsFromLiteral lit1) == sort expectedL1
test2 = sort (extractSymbolsFromLiteral lit2) == sort expectedL2
test3 = sort (extractSymbolsFromLiteral lit3) == sort expectedL3
test4 = sort (extractSymbolsFromLiteral lit4) == sort expectedL4
test5 = sort (extractSymbolsFromLiteral lit5) == sort expectedL5


runExtractSymbolsFromLiteralTests = concat
    [
        "\n\n Running Literal Symbol Extraction Tests", 
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5
    ]