{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use ++" #-}
module Substitution.TermSubstitutionTests where
import FOL
import Substitution (termSubstituition)



term1 = Var "X"
subTerm1 = Var "Y"
subFunc1 x = if x == Var "X" then  Var "Y" else x

term2 = Fn("F", [Var "X"])
subTerm2 = Fn("F", [Var "Y"])

term3 = Fn("F", [Fn ("G", [Var "X"])])
subTerm3 = Fn("F", [Fn ("G", [Var "Y"])])

term4 = Var "Z"
subTerm4 = Var "Z"

term5 = Fn("F", [Var "X", Var "Z"])
subTerm5 = Fn("F", [Var "Y", Var "Z"])

term6 = Fn("F", [Fn ("G", [Var "X", Var "Z"])])
subTerm6 = Fn("F", [Fn ("G", [Var "Y", Var "Z"])])

term7 = Fn("F", [Fn ("G", [Var "X", Fn("H", [Var "X"])])])
subTerm7 = Fn("F", [Fn ("G", [Var "Y", Fn("H", [Var "Y"])])])

term8 = Var "X"
subTerm8 = Fn ("F", [])
subFunc2 x = if x == Var "X" then  Fn ("F", []) else x

term9 = Fn("G", [Var "X"])
subTerm9 = Fn("G", [Fn ("F", [])])


test1 = termSubstituition subFunc1 term1  == subTerm1
test2 = termSubstituition subFunc1 term2 == subTerm2
test3 = termSubstituition subFunc1 term3 == subTerm3
test4 = termSubstituition subFunc1 term4 == subTerm4
test5 = termSubstituition subFunc1 term5 == subTerm5
test6 = termSubstituition subFunc1 term6 == subTerm6
test7 = termSubstituition subFunc1 term7 == subTerm7
test8 = termSubstituition subFunc2 term8 == subTerm8
test9 = termSubstituition subFunc2 term9 == subTerm9



runTermSubstitutionTests  = concat 
    [
        "\n\n Running Term Substitution Tests", 
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5,
        "\n Test 6: " ++ show test6,
        "\n Test 7: " ++ show test7,
        "\n Test 8: " ++ show test8,
        "\n Test 9: " ++ show test9
    ]