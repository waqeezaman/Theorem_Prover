{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use null" #-}
module Unification.VariablesInClauseTests (runVariablesInClauseTests) where 
import FOL
import Unification (variablesInClause)
import qualified Data.Set as Set


term1 = Var "X"
term2 = Var "Y"
term3 = Var "Z"
term4 = Fn("F", [term1])
term5 = Fn("G", [Fn("F", [term2]), term3])
term6= Fn("A", [])
term7= Fn("H", [term3])


clause1 = []
clause2 = [Pos(R("P", [term1]))]
clause3 = [Neg(R("Q", [term5]))]
clause4 = [Pos(R("P", [term3]))]
clause5 = [Pos(R("Q",[term4]))]
clause6 = [Neg(R("R",[term1, term7]))]
clause7 = [Neg(R("R",[term5, term2])),Pos(R("P", [term6]))]
clause8 = [Pos(R("P", [term7])), Neg(R("Q", [term2])), Pos(R("P", [term7]))]
clause9 = [Neg(R("R",[term1, term6])), Pos(R("P", [term4]))]
clause10 = [Pos(R("P", [term7])), Pos(R("Q", [term1, term2, term6, term4])), Pos(R("P", [term5]))]


test1 = variablesInClause clause1 == Set.empty
test2 = variablesInClause clause2 == Set.singleton "X"
test3 = variablesInClause clause3 == Set.fromList ["Y", "Z"]
test4 = variablesInClause clause4 == Set.singleton "Z"
test5 = variablesInClause clause5 == Set.singleton "X"
test6 = variablesInClause clause6 == Set.fromList ["X", "Z"]
test7 = variablesInClause clause7 == Set.fromList ["Y", "Z"]
test8 = variablesInClause clause8 == Set.fromList ["Y", "Z"]
test9 = variablesInClause clause9 == Set.fromList ["X"]
test10 = variablesInClause clause10 == Set.fromList ["X", "Y", "Z"]

 


runVariablesInClauseTests = concat 
    [
        "\n\n Running Variables In Clause Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5,
        "\n Test 6: " ++ show test6,
        "\n Test 7: " ++ show test7,
        "\n Test 8: " ++ show test8,
        "\n Test 9: " ++ show test9,
        "\n Test 10: " ++ show test10
    ]