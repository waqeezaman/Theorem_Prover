{-# OPTIONS_GHC -Wno-missing-signatures #-}
module CNFTests where

import CNF ( toCNF )
import FOL ( Formula(And, Atom, Not, Or), Predicate(R) )

p = Atom(R("P", []))
a = Atom(R("A", []))
b = Atom(R("B", []))
c = Atom(R("C", []))
d = Atom(R("D", []))
e = Atom(R("E", []))


formula1 = p `Or` (p `And` p)
cnfFormula1 = (p `Or` p) `And` (p `Or` p)


formula2 = (p `And` p) `Or` p
cnfFormula2 = (p `Or` p) `And` (p `Or` p)

formula3 = (p `And` p) `Or` Not p
cnfFormula3 = (p `Or` Not p) `And` (p `Or` Not p)

formula4 = p `Or` (p `And` (p `Or` p))
cnfFormula4 =   (p `Or` p) `And` (p `Or` (p `Or` p))

formula5 = (a `And` (b `And` c)) `Or` (d `And` Not e)
cnfFormula5 =   ((a `Or` d)  `And`
                ((b `Or` d)  `And`
                (c `Or` d)))  `And`
                ((a `Or` Not e) `And`
                ((b `Or` Not e) `And`
                (c `Or` Not e)))



test1 = cnfFormula1 == toCNF formula1
test2 = cnfFormula2 == toCNF formula2
test3 = cnfFormula3 == toCNF formula3
test4 = cnfFormula4 == toCNF formula4
test5 = cnfFormula5 == toCNF formula5


runCNFTests = concat 
    [
        "\n\n CNF Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5 
    ]

