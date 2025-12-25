{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Unification.StandardiseApartTests where 

import Unification 
import FOL



formulaP1 = Atom(R("P", [Var "X", Var "Y"]))
formulaQ1 = Atom(R("P", [Var "X", Var "Y"]))
expectedFormulaQ1 = Atom(R("P", [Var "X#", Var "Y#"]))

formulaP2 = Not(Atom(R("P", [Var "X", Var "Y"])))
formulaQ2 = Atom(R("P", [Var "X", Var "Y"]))
expectedFormulaQ2 = Atom(R("P", [Var "X#", Var "Y#"]))

formulaP3 = Atom(R("P", [Var "X", Var "X"])) `And` Atom(R("P", [Var "Y#", Var "Y"]))
formulaQ3 = Not(Atom(R("P", [Var "X", Var "Y#"])))
expectedFormulaQ3 = Not(Atom(R("P", [Var "X#", Var "Y##"])))

formulaP4 = Atom(R("P", [Var "Y#", Var "X"])) `Or` Atom(R("P", [Var "Y##", Var "Y###"]))
formulaQ4 = Not(Atom(R("Q", [Var "X", Var "Y###", Var "X#"])))
expectedFormulaQ4 = Not(Atom(R("Q", [Var "X##", Var "Y####", Var "X#"])))

formulaP5 = Atom(R("P", [Var "X", Var "Y"])) `And` Atom(R("P", [Var "Z", Var "W"]))
formulaQ5 = Atom(R("P", [Var "X", Var "Y"])) `Or` Atom(R("P", [Var "Z", Var "W"]))
expectedFormulaQ5 = Atom(R("P", [Var "X#", Var "Y#"])) `Or` Atom(R("P", [Var "Z#", Var "W#"]))

test1 = standardiseApart formulaP1 formulaQ1 == expectedFormulaQ1 
test2 = standardiseApart formulaP2 formulaQ2 == expectedFormulaQ2 
test3 = standardiseApart formulaP3 formulaQ3 == expectedFormulaQ3 
test4 = standardiseApart formulaP4 formulaQ4 == expectedFormulaQ4 
test5 = standardiseApart formulaP5 formulaQ5 == expectedFormulaQ5 


runStandardiseApartTests = concat
    [
        "\n\n Running Standardise Apart Tests", 
        "\n Test 1: " ++ show test1, 
        "\n Test 2: " ++ show test2, 
        "\n Test 3: " ++ show test3, 
        "\n Test 4: " ++ show test4, 
        "\n Test 5: " ++ show test5
    ]