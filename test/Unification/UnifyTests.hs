{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use ++" #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Unification.UnifyTests where
import qualified Data.Map as Map
import FOL ( Predicate(R), Term(Var, Fn) ) 
import Unification ( unify )


predicate1 = R ("P", [Var "X", Var "Y", Fn("F", [Fn ("A", [])])])
predicate2 = R ("P", [Var "Z", Fn("A", []), Var "Z"])
expectedSub1 = Just (Map.fromList 
    [
        (Var "X", Fn ("F", [Fn ("A", [])])),
        (Var "Y", Fn("A", [])),
        (Var "Z", Fn ("F", [Fn ("A", [])]))
    ])

predicate3 = R ("P", [Var "X", Fn("F", [])])
predicate4 = R ("P", [Var "Z", Var "Z"])
expectedSub2 = Just (Map.fromList
    [
        (Var "X", Fn("F", [])),
        (Var "Z", Fn("F", []))
    ])

predicate5 = R ("P", [Var "X", Fn("F", [Var "Y"]), Fn("A", [])])
predicate6 = R ("P", [Var "Z", Var "Z", Var "Y"])
expectedSub3 = Just (Map.fromList
    [
        (Var "X", Fn("F", [Fn("A", [])])),
        (Var "Z", Fn("F", [Fn("A", [])])),
        (Var "Y", Fn("A", []))
    ])

predicate7 = R ("P", [Var "X", Fn("F", [Var "Y"]), Fn("F", [Fn("G", [Var "K"])])])
predicate8 = R ("P", [Var "Z", Var "Z", Var "Y"])
expectedSub4 = Just (Map.fromList
    [
        (Var "X", Fn("F", [Fn("F", [Fn("G", [Var "K"])])])),
        (Var "Z", Fn("F", [Fn("F", [Fn("G", [Var "K"])])])),
        (Var "Y", Fn("F", [Fn("G", [Var "K"])]))
    ])


test1 = unify predicate1 predicate2 == expectedSub1
test2 = unify predicate3 predicate4 == expectedSub2
test3 = unify predicate5 predicate6 == expectedSub3
test4 = unify predicate7 predicate8 == expectedSub4

runUnifyTests = concat 
    [
        "\n\n Running Unify Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4
    ]
