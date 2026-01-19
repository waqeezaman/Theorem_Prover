{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.ExtractSymbolsFromTermTests (runExtractSymbolsFromTermTests) where


import FOL (Term(..))
import Subsumption.SubsumptionFilter (extractSymbolsFromTerm)
import Data.List (sort)

term1 = Var "X"
expected1 = []

term2 = Fn ("a", [])
expected2 = ["_F_a"]

term3 = Fn ("f", [Var "X", Fn ("b", [])])
expected3 = ["_F_f", "_F_b"]

term4 = Fn ("f", [Fn ("g", [Fn ("h", [Var "Z"])])])
expected4 = ["_F_f", "_F_g", "_F_h"]

term5 = Fn ("f", [Fn ("a", []), Fn ("a", []), Var "X"])
expected5 = ["_F_f", "_F_a", "_F_a"]


test1 = sort (extractSymbolsFromTerm term1) == sort expected1
test2 = sort (extractSymbolsFromTerm term2) == sort expected2
test3 = sort (extractSymbolsFromTerm term3) == sort expected3
test4 = sort (extractSymbolsFromTerm term4) == sort expected4
test5 = sort (extractSymbolsFromTerm term5) == sort expected5

runExtractSymbolsFromTermTests = concat
    [
        "\n\n Running Term Symbol Extraction Tests", 
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5
    ]