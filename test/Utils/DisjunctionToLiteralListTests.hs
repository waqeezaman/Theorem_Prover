{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Utils.DisjunctionToLiteralListTests where
import FOL
import Utils (disjunctionToLiteralList)

atom1 = Atom(R ("P", [Var "X"]))
atom2 = Atom(R ("Q", [Var "X"]))
atom3 = Not (Atom(R ("L", [Var "X"])))

literal1 = Pos (R("P", [Var "X"]))
literal2 = Pos (R("Q", [Var "X"]))
literal3 = Neg (R("L", [Var "X"]))

disjunction1 = atom1 `Or` atom2
literalList1 = [literal1, literal2]

disjunction2 = atom1 `Or` atom3
literalList2 = [literal1, literal3]

disjunction3 = atom3 `Or` atom3
literalList3 = [literal3, literal3]

disjunction4 = atom1 `Or` atom2 `Or` atom3
literalList4 = [literal1, literal2, literal3]

disjunction5 = atom1 
literalList5 = [literal1]

disjunction6 = atom3 
literalList6 = [literal3]

test1 = disjunctionToLiteralList disjunction1 == literalList1
test2 = disjunctionToLiteralList disjunction2 == literalList2
test3 = disjunctionToLiteralList disjunction3 == literalList3
test4 = disjunctionToLiteralList disjunction4 == literalList4
test5 = disjunctionToLiteralList disjunction5 == literalList5
test6 = disjunctionToLiteralList disjunction6 == literalList6


runDisjunctionToLiteralListTests = concat 
    [
        "\n\n Running Disjunction To Literal List Tests: ", 
        "\n Test 1: " ++ show test1, 
        "\n Test 2: " ++ show test2, 
        "\n Test 3: " ++ show test3, 
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5, 
        "\n Test 6: " ++ show test6
    ]

