{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use null" #-}
module Resolution.ResolveTests (runResolveTests) where
import FOL
import Resolution (resolve)
import Utils (makeSetOfSets)

literal1 = Pos(R("P", [Var "X"]))
literal2 = Neg(R("P", [Var "Z"]))
literal3 = Pos(R("Q", [Var "Y"]))
literal4 = Neg(R("Q", [Fn("A", [])]))
literal5 = Neg(R("Q", [Fn("B", [])]))
literal6 = Neg(R("P", [Fn("F", [Var "X"])]))

clause1 = [literal1]
clause2 = [literal2]

clause3 = [literal3]
clause4 = [literal4]
clause5 = [literal5]

clause6 = [literal4, literal5]

test1 = resolve clause1 clause2 == [[]]
test2 = resolve clause3 clause4 == [[]]
test3 = resolve clause3 clause5 == [[]]

test4 = resolve clause4 clause5 == []

test5 = makeSetOfSets (resolve clause3 clause6) == makeSetOfSets [[literal5], [literal4]]
test6 = resolve [literal1] [literal6] == []

runResolveTests = concat 
    [
        "\n\n Running Resolve Tests",
        "\n Test 1:" ++ show test1,
        "\n Test 2:" ++ show test2,
        "\n Test 3:" ++ show test3,
        "\n Test 4:" ++ show test4,
        "\n Test 5:" ++ show test5,
        "\n Test 6:" ++ show test6
    ]