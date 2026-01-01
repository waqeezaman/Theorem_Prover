{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use null" #-}
module Resolution.OpposingPolarityPairsTests (runOpposingPolarityPairsTests) where
import FOL
import Resolution (opposingPolarityPairs)

literal1 = Pos (R("P", [Var "X"]))
literal2 = Pos (R("Q", [Var "X"]))
literal3 = Neg (R("R", [Var "X"]))
literal4 = Neg (R("S", [Var "X"]))

test1 = opposingPolarityPairs [] == []
test2 = opposingPolarityPairs [(literal1, literal2)] == []
test3 = opposingPolarityPairs [(literal3, literal4)] == []
test4 = opposingPolarityPairs [(literal1, literal3)] == [(literal1, literal3)]
test5 = opposingPolarityPairs [(literal2, literal4)] == [(literal2, literal4)]
test6 = opposingPolarityPairs [(literal1, literal4)] == [(literal1, literal4)]
test7 = opposingPolarityPairs [(literal2, literal3)] == [(literal2, literal3)]
test8 = opposingPolarityPairs [(literal1, literal2), (literal3, literal4)] == []
test9 = opposingPolarityPairs [(literal1, literal3), (literal2, literal4)] == [(literal1, literal3), (literal2, literal4)]
test10 = opposingPolarityPairs [(literal1, literal3), (literal1, literal2)] == [(literal1, literal3)]

runOpposingPolarityPairsTests = concat
    [
        "\n\n Running Opposing Polarity Pairs Tests",
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