{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use null" #-}
module Resolution.ApplyResolutionTests (runApplyResolutionTests) where
import qualified Data.Map as Map
import FOL
import Resolution (applyResolution)

sub = Map.fromList [(Var "X", Var "Z"), (Var "Y", Fn ("A", []))]

literal1 = Pos (R ("P", [Var "X"]))
literal2 = Neg (R ("P", [Var "Z"]))
literal3 = Pos (R ("Q", [Var "Y"]))
literal4 = Neg (R ("Q", [Fn ("A", [])]))

clause1 = [literal1]
clause2 = [literal2]
clause3 = [literal3]
clause4 = [literal4]
clause5 = [literal1, literal2]
clause6 = [literal3, literal4]
clause7 = [literal1, literal2, literal3]
clause8 = [literal1, literal2, literal4]
clause9 = [literal2, literal3, literal4]
clause10 = [literal1, literal3, literal4]
clause11 = [literal1, literal2, literal3, literal4]
clause12 = [literal1, literal3]
clause13 = [literal2, literal1]


test1 = applyResolution clause1 clause2 (literal1, literal2, sub) == []
test2 = applyResolution clause3 clause4 (literal3, literal4, sub) == []
test3 = applyResolution clause1 clause5 (literal1, literal2, sub) == [Pos (R ("P", [Var "Z"]))]
test4 = applyResolution clause6 clause3 (literal4, literal3, sub) == [Pos (R ("Q", [Fn ("A", [])]))]
test5 = applyResolution clause7 clause5 (literal1, literal2, sub) ==
    [
        Neg (R ("P", [Var "Z"])),
        Pos (R ("Q", [Fn ("A", [])])),
        Pos (R ("P", [Var "Z"]))
    ]
test6 = applyResolution clause7 clause8 (literal3, literal4, sub) ==
    [
        Pos (R ("P", [Var "Z"])),
        Neg (R ("P", [Var "Z"])),
        Pos (R ("P", [Var "Z"])),
        Neg (R ("P", [Var "Z"]))
    ]
test7 = applyResolution clause9 clause10 (literal3, literal4, sub) ==
    [
        Neg (R ("P", [Var "Z"])),
        Neg (R ("Q", [Fn ("A", [])])),
        Pos (R ("P", [Var "Z"])),
        Pos (R ("Q", [Fn ("A", [])]))
    ]
test8 = applyResolution clause10 clause11 (literal3, literal4, sub) ==
    [
        Pos (R ("P", [Var "Z"])),
        Neg (R ("Q", [Fn ("A", [])])),
        Pos (R ("P", [Var "Z"])),
        Neg (R ("P", [Var "Z"])),
        Pos (R ("Q", [Fn ("A", [])]))
    ]
test9 = applyResolution clause12 clause13 (literal1, literal2, sub) == [Pos (R ("Q", [Fn ("A", [])])), Pos (R ("P", [Var "Z"]))]

runApplyResolutionTests = concat
    [
        "\n\n Running Apply Resolution Tests",
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