{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant ==" #-}
{-# HLINT ignore "Redundant bracket" #-}
module Unification.FormulaContainsVarTests where 

import FOL 
import Unification

formula1 = (Atom(R("P", [Var "X"])))
formula2 = Not (Atom(R("P", [Var "X"])))
formula3 = (Atom(R("P", [Var "X"]))) `And` (Atom(R("P", [Var "Y"])))
formula4 = (Atom(R("P", [Var "X"]))) `Or` (Atom(R("P", [Var "Y"])))
formula5 = (Atom(R("P", [Var "X"]))) `Imp` (Atom(R("P", [Var "Y"])))
formula6 = (Atom(R("P", [Var "X"]))) `Iff` (Atom(R("P", [Var "Y"])))
formula7 = Exists "X" (Atom(R("P", [Var "X"])))
formula8 = Forall "X" (Atom(R("P", [Var "X"])))

test1 = formulaContainsVar "X" formula1 == True
test2 = formulaContainsVar "Y" formula1 == False

test3 = formulaContainsVar "X" formula2 == True
test4 = formulaContainsVar "Y" formula2 == False

test5 = formulaContainsVar "X" formula3 == True
test6 = formulaContainsVar "Y" formula3 == True
test7 = formulaContainsVar "Z" formula3 == False

test8 = formulaContainsVar "X" formula4 == True
test9 = formulaContainsVar "Y" formula4 == True
test10 = formulaContainsVar "Z" formula4 == False

test11 = formulaContainsVar "X" formula5 == True
test12 = formulaContainsVar "Y" formula5 == True
test13 = formulaContainsVar "Z" formula5 == False

test14 = formulaContainsVar "X" formula6 == True
test15 = formulaContainsVar "Y" formula6 == True
test16 = formulaContainsVar "Z" formula6 == False

test17 = formulaContainsVar "X" formula7 == True
test18 = formulaContainsVar "Y" formula7 == False

test19 = formulaContainsVar "X" formula8 == True
test20 = formulaContainsVar "Y" formula8 == False


runFormulaContainsVarTests = concat
    [
        "\n\n Running Formula Contains Var Tests",
        "\n Test 1 :" ++ show test1,
        "\n Test 2 :" ++ show test2,
        "\n Test 3 :" ++ show test3,
        "\n Test 4 :" ++ show test4,
        "\n Test 5 :" ++ show test5,
        "\n Test 6 :" ++ show test6,
        "\n Test 7 :" ++ show test7,
        "\n Test 8 :" ++ show test8,
        "\n Test 9 :" ++ show test9,
        "\n Test 10 :" ++ show test10,
        "\n Test 11 :" ++ show test11,
        "\n Test 12 :" ++ show test12,
        "\n Test 13 :" ++ show test13,
        "\n Test 14 :" ++ show test14,
        "\n Test 15 :" ++ show test15,
        "\n Test 16 :" ++ show test16,
        "\n Test 17 :" ++ show test17,
        "\n Test 18 :" ++ show test18,
        "\n Test 19 :" ++ show test19,
        "\n Test 20 :" ++ show test20
    ]