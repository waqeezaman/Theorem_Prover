{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Utils.CNFToClausalFormTests where 
import FOL
import Utils (fromCNFToClausalForm)

atom1 = Atom(R("P", [Var "X"]))
atom2 = Atom(R("Q", [Var "X"]))
atom3 = Not (Atom(R("L", [Var "X"])))

literal1 = Pos (R("P", [Var "X"]))
literal2 = Pos (R("Q", [Var "X"]))
literal3 = Neg (R("L", [Var "X"]))

formula1 = atom1 `And` atom2 `And` atom3
clausal1 = [[literal1], [literal2], [literal3]]

formula2 = atom1 `Or` atom2
clausal2 = [[literal1, literal2]]

formula3 = atom1
clausal3 = [[literal1]]

formula4 = atom3 
clausal4 = [[literal3]]

formula5 = (atom1 `Or` atom2) `And` (atom3 `Or` atom2) `And` (atom1 `Or` atom3)
clausal5 = [[literal1, literal2], [literal3, literal2], [literal1, literal3]]

test1 = fromCNFToClausalForm formula1 == clausal1
test2 = fromCNFToClausalForm formula2 == clausal2
test3 = fromCNFToClausalForm formula3 == clausal3
test4 = fromCNFToClausalForm formula4 == clausal4
test5 = fromCNFToClausalForm formula5 == clausal5


runCNFToClausalFormTests = concat 
    [
        "\n\n Running CNF To Clausal Form Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5
    ]