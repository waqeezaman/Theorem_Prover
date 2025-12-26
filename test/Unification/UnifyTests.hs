{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use ++" #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Unification.UnifyTests where
import qualified Data.Map as Map
import FOL ( Formula(Atom), Predicate(R), Term(Var, Fn) ) 
import Unification ( unify )


atom1 = Atom(R ("P", [Var "X", Var "Y", Fn("F", [Fn ("A", [])])]))
atom2 = Atom(R ("P", [Var "Z", Fn("A", []), Var "Z"]))
expectedSub1 = Just (Map.fromList 
    [
        (Var "X", Fn ("F", [Fn ("A", [])])),
        (Var "Y", Fn("A", [])),
        (Var "Z", Fn ("F", [Fn ("A", [])]))
    ])

atom3 = Atom(R ("P", [Var "X", Fn("F", [])]))
atom4 = Atom(R ("P", [Var "Z", Var "Z"]))
expectedSub2 = Just (Map.fromList
    [
        (Var "X", Fn("F", [])),
        (Var "Z", Fn("F", []))
    ])

atom5 = Atom(R ("P", [Var "X", Fn("F", [Var "Y"]), Fn("A", [])]))
atom6 = Atom(R ("P", [Var "Z", Var "Z", Var "Y"]))
expectedSub3 = Just (Map.fromList
    [
        (Var "X", Fn("F", [Fn("A", [])])),
        (Var "Z", Fn("F", [Fn("A", [])])),
        (Var "Y", Fn("A", []))
    ])

atom7 = Atom(R ("P", [Var "X", Fn("F", [Var "Y"]), Fn("F", [Fn("G", [Var "K"])])]))
atom8 = Atom(R ("P", [Var "Z", Var "Z", Var "Y"]))
expectedSub4 = Just (Map.fromList
    [
        (Var "X", Fn("F", [Fn("F", [Fn("G", [Var "K"])])])),
        (Var "Z", Fn("F", [Fn("F", [Fn("G", [Var "K"])])])),
        (Var "Y", Fn("F", [Fn("G", [Var "K"])]))
    ])


test1 = unify atom1 atom2 == expectedSub1
test2 = unify atom3 atom4 == expectedSub2
test3 = unify atom5 atom6 == expectedSub3
test4 = unify atom7 atom8 == expectedSub4

runUnifyTests = concat 
    [
        "\n\n Running Unify Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4
    ]
