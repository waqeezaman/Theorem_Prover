{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Factoring.ApplyFactorisationTests (runApplyFactoringTests) where
import FOL
import Factoring (applyFactorisation)
import qualified Data.Map as Map
import Utils (removeFirstOccurenceFromClause)
import Unification (applySubToClause)
import qualified Data.Set as Set



literal1 = Pos (R ("P", [Var "X", Fn ("A", [])]))
literal2 = Pos (R ("P", [Var "Y", Fn ("A", [])]))

literal3 = Pos(R("Q", [Var "X"]))
literal4 = Pos(R("Q", [Var "Y"]))

clause1 = [literal1, literal2]
clause2 = [literal3, literal4]

clause3 = [literal1, literal2, literal3, literal4]

sub = Map.fromList [(Var "X", Var "Y")]

test1 = applyFactorisation clause1 (literal1, literal2, sub)  == [literal2]
test2 = applyFactorisation clause2 (literal3, literal4, sub) == [literal4]
test3 = Set.fromList(applyFactorisation clause3 (literal1, literal2, sub)) == Set.fromList [literal2, Pos(R("Q", [Var "Y"])), Pos(R("Q", [Var "Y"]))]
test4 = Set.fromList (applyFactorisation clause3 (literal3, literal4, sub)) == Set.fromList [Pos (R ("P", [Var "Y", Fn ("A", [])])), Pos (R ("P", [Var "Y", Fn ("A", [])])), literal4]



runApplyFactoringTests = concat
    [
        "\n\n Running Apply Factorisation Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n output 4: " ++ show (applyFactorisation clause3 (literal3, literal4, sub))
    ]