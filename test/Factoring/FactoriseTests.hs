{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use null" #-}
module Factoring.FactoriseTests (runFactoriseTests) where 
import FOL ( Literal(Pos, Neg), Predicate(R), Term(Fn, Var) )
import Factoring (factorise)
import Utils (makeSetOfSets)

literal1 = Pos(R("P", [Var "X", Fn("A", [])]))
literal2 = Pos(R("P", [Var "Y", Fn("A", [])]))
literal3 = Neg(R("Q", [Fn("F", [Var "X"])]))
literal4 = Neg(R("Q", [Fn("F", [Fn("A", [])])]))
literal5 = Pos(R("R", [Fn("A", [])]))
literal6 = Pos(R("R", [Fn("B", [])]))

clause1 = []
clause2 = [literal1]
clause3 = [literal1, literal2]
clause4 = [literal3, literal4]
clause5 = [literal1, literal2, literal3, literal4]
clause6 = [literal5, literal6]
clause7 = [literal1, literal2, literal3, literal4, literal5, literal6]


test1 = factorise clause1 == []
test2 = factorise clause2 == []
test3 = factorise clause3 == [[literal2]]
test4 = factorise clause4 == [[literal4]]
test5 = makeSetOfSets(factorise clause5) == makeSetOfSets [
    [
        literal2,
        Neg(R("Q", [Fn("F", [Var "Y"])])),
        Neg(R("Q", [Fn("F", [Fn("A", [])])]))
    ],
    [
        literal4,
        Pos(R("P", [Fn("A", []), Fn("A", [])])),
        Pos(R("P", [Var "Y", Fn("A", [])]))
    ]]
test6 = factorise clause6 == []
test7 = makeSetOfSets (factorise clause7) == makeSetOfSets [
    [
        literal2,
        Neg(R("Q", [Fn("F", [Var "Y"])])),
        Neg(R("Q", [Fn("F", [Fn("A", [])])])),
        Pos(R("R", [Fn("A", [])])),
        Pos(R("R", [Fn("B", [])]))
    ],
    [
        literal4,
        Pos(R("P", [Fn("A", []), Fn("A", [])])),
        Pos(R("P", [Var "Y", Fn("A", [])])),
        Pos(R("R", [Fn("A", [])])),
        Pos(R("R", [Fn("B", [])]))
    ]]


runFactoriseTests = concat
    [
        "\n\n Running Factorise Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5,
        "\n Test 6: " ++ show test6,
        "\n Test 7: " ++ show test7
    ]