{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
module Unification.TermUnificationTests where

import qualified Data.Map as Map

import FOL (Term(..))
import Unification (unifyTerms)

terms1 = [(Var "X", Var "Y")]
expectedSub1 = Just (Map.fromList [(Var "X", Var "Y")])

terms2 = [(Var "X", Fn ("F", []))]
expectedSub2 = Just(Map.fromList [(Var "X", Fn ("F", []))])

terms3 = [(Fn ("F", []), Var "X")]
expectedSub3 = Just(Map.fromList [(Var "X", Fn ("F", []))])

terms4 = []
expectedSub4 = Just Map.empty

terms5 = [(Var "X", Var "X")]
expectedSub5 = Just Map.empty

terms6 = [(Fn ("F", []), Fn ("F", []))]
expectedSub6 = Just Map.empty

terms7 = [(Var "X", Fn ("F", [Var "X"]))]
expectedSub7 = Nothing

terms8 = [(Fn ("F", []), Fn ("G", []))]
expectedSub8 = Nothing

terms9 = [(Fn ("F", [Var "X"]), Fn ("F", [Var "X", Var "X"]))]
expectedSub9 = Nothing

terms10 = [(Fn ("F", [Var "X", Var "Y"]), Fn ("F", [Fn ("G", []), Fn ("H", [])]))]
expectedSub10 = Just (Map.fromList [(Var "X", Fn ("G", [])), (Var "Y", Fn("H",[]))])

terms11 = [(Fn ("F", [Var "X", Fn ("H", [])]), Fn("F", [Fn ("G", []), Var "Y"]))]
expectedSub11 = Just(Map.fromList [(Var "X", Fn ("G", [])), (Var "Y", Fn("H",[]))])

terms12 = [
        (Var "X", Fn("A", [])),
        (Fn("F", [Var "Y"]), Fn("F", [Fn("G", [Var "Z"])]))
    ]
expectedSub12 = Just (Map.fromList 
    [
        (Var "X", Fn("A", [])),
        (Var "Y", Fn("G", [Var "Z"]))
    ])

terms13 = [
        (Fn("A", []), Fn("A", [])),
        (Fn("G", [Var "X", Fn("A", [])]), Fn("G", [Fn ("F", [Fn("B", [])]), Fn("A", [])])),
        (Fn("F", [Var "Y"]), Var "X")
    ] 
expectedSub13 = Just (Map.fromList 
    [
        (Var "X", Fn("F", [Fn ("B", [])])),
        (Var "Y", Fn("B", []))
    ])

terms14 = [
        (Fn("H", [Var "X"]), Fn("F", [Fn("A", [])])),
        (Fn("C", []), Var "Y")
    ]
expectedSub14 = Nothing


test1 = unifyTerms terms1 Map.empty == expectedSub1
test2 = unifyTerms terms2 Map.empty == expectedSub2
test3 = unifyTerms terms3 Map.empty == expectedSub3
test4 = unifyTerms terms4 Map.empty == expectedSub4
test5 = unifyTerms terms5 Map.empty == expectedSub5
test6 = unifyTerms terms6 Map.empty == expectedSub6
test7 = unifyTerms terms7 Map.empty == expectedSub7
test8 = unifyTerms terms8 Map.empty == expectedSub8
test9 = unifyTerms terms9 Map.empty == expectedSub9
test10 = unifyTerms terms10 Map.empty == expectedSub10
test11 = unifyTerms terms11 Map.empty == expectedSub11
test12 = unifyTerms terms12 Map.empty == expectedSub12
test13 = unifyTerms terms13 Map.empty == expectedSub13
test14 = unifyTerms terms14 Map.empty == expectedSub14


runTermUnificationTests = concat
    [
        "\n\n Running Term Unification Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5,
        "\n Test 6: " ++ show test6,
        "\n Test 7: " ++ show test7,
        "\n Test 8: " ++ show test8,
        "\n Test 9: " ++ show test9,
        "\n Test 10: " ++ show test10,
        "\n Test 11: " ++ show test11,
        "\n Test 12: " ++ show test12,
        "\n Test 13: " ++ show test13,
        "\n Test 14: " ++ show test14
    ]
