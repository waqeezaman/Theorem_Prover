{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Unification.PredicateUnificationTests where 

import qualified Data.Map as Map
import FOL
import Unification 


predicate1 = R ("P", []) 
predicate2 = R ("P", [])
expectedSub1 = Just Map.empty


predicate3 = R ("P", [])
predicate4 = R ("Q", [])
expectedSub2 = Nothing

predicate5 = R ("P", [Var "X"])
predicate6 = R ("P", [Var "Y"])
expectedSub3 = Just (Map.fromList [(Var "X", Var "Y")])


predicate7 = R ("P", [Var "X", Var "Y"])
predicate8 = R ("P", [Var "X"])
expectedSub4 = Nothing 

predicate9 = R ("P", [Var "X", Var "Y"])
predicate10 = R ("P", [Var "Z", Fn("A", [])])
expectedSub5 = Just (Map.fromList [(Var "X", Var "Z"), (Var "Y", Fn("A", []))])


test1 = unifyPredicates predicate1 predicate2 == expectedSub1
test2 = unifyPredicates predicate3 predicate4 == expectedSub2
test3 = unifyPredicates predicate5 predicate6 == expectedSub3
test4 = unifyPredicates predicate7 predicate8 == expectedSub4
test5 = unifyPredicates predicate9 predicate10 == expectedSub5


runPredicateUnificationTests = concat
    [
        "\n\n Running Predicate Unification Tests", 
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5
    ]

