{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant ==" #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Unification.TermContainsVarTests where 

import FOL
import Unification

term1 = Var "X"

term2 = Fn("F", [Var "X"])

term3 = Fn("G", [Var "X", Var "Y"])

term4 = Fn("H", [])

test1 = termContainsVar "X" term1 == True 
test2 = termContainsVar "Y" term1 == False

test3 = termContainsVar "X" term2 == True
test4 = termContainsVar "Y" term2 == False

test5 = termContainsVar "X" term3 == True
test6 = termContainsVar "Y" term3 == True
test7 = termContainsVar "Z" term3 == False

test8 = termContainsVar "X" term4 == False

runTermContainsVarTests = concat 
    [
        "\n\n Runnning Term Contains Var Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5,
        "\n Test 6: " ++ show test6,
        "\n Test 7: " ++ show test7,
        "\n Test 8: " ++ show test8
    ]