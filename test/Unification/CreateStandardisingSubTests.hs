{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Unification.CreateStandardisingSubTests (runCreateStandardisingSubTests) where
import qualified Data.Map as Map
import Unification (createStandardisingSub)
import FOL


test1 = 
    createStandardisingSub
    ["X", "Y", "Z"]
    ["X", "Y", "Z"]
    Map.empty
    == Map.fromList [(Var "X",Var "X#"), (Var "Y",Var "Y#"), (Var "Z",Var "Z#")]

test2 = 
    createStandardisingSub
    ["X"]
    ["X", "X#"]
    Map.empty 
    == Map.fromList [(Var "X", Var "X##")]

test3 = createStandardisingSub
        []
        []
        Map.empty
        == Map.empty

test4 = createStandardisingSub 
        []
        ["X", "Y"]
        Map.empty
        == Map.empty

test5 = createStandardisingSub
        ["X", "X#"]
        ["X", "X#", "Y"]
        Map.empty
        == Map.fromList [(Var "X", Var "X##"), (Var "X#", Var "X###")]

runCreateStandardisingSubTests = concat 
    [
        "\n\n Running Create Standardising Sub Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5
    ]
