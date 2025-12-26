{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Unification.AtomUnificationTests where 

import qualified Data.Map as Map
import FOL
import Unification (unifyAtoms)


atom1 = Atom(R ("P", [])) 
atom2 = Atom(R ("P", []))
expectedSub1 = Just Map.empty


atom3 = Atom(R ("P", []))
atom4 = Atom(R ("Q", []))
expectedSub2 = Nothing

atom5 = Atom(R ("P", [Var "X"]))
atom6 = Atom(R ("P", [Var "Y"]))
expectedSub3 = Just (Map.fromList [(Var "X", Var "Y")])


atom7 = Atom(R ("P", [Var "X", Var "Y"]))
atom8 = Atom(R ("P", [Var "X"]))
expectedSub4 = Nothing 

atom9 = Atom(R ("P", [Var "X", Var "Y"]))
atom10 = Atom(R ("P", [Var "Z", Fn("A", [])]))
expectedSub5 = Just (Map.fromList [(Var "X", Var "Z"), (Var "Y", Fn("A", []))])


test1 = unifyAtoms atom1 atom2 == expectedSub1
test2 = unifyAtoms atom3 atom4 == expectedSub2
test3 = unifyAtoms atom5 atom6 == expectedSub3
test4 = unifyAtoms atom7 atom8 == expectedSub4
test5 = unifyAtoms atom9 atom10 == expectedSub5


runAtomUnificationTests = concat
    [
        "\n\n Running Atom Unification Tests", 
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5
    ]

