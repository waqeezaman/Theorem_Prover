module PrenexTests where 

import FOL 
import Prenex
import FOL (prettyPrintFormula, Formula (Not))
import Simplification (folSimplify, nnf)

p = Atom (R("pred", [Var "P"]))
q = Atom (R("pred", [Var "Q"]))

p' = Atom(R("pred", [Var "P#"]))


formula1 = (Forall "X" p) `And` q
pnfFormula1 = Forall "X" (p `And` q)

formula2 = (Forall "P" p) `And` p
pnfFormula2 = Forall "P#" (p' `And` p)

formula3 = p `And` (Forall "P" p)
pnfFormula3 = Forall "P#" (p `And` p')

formula4 = (Forall "P" p) `Or` p
pnfFormula4 = Forall "P#" (p' `Or` p)

formula5 = p `Or` (Forall "P" p)
pnfFormula5 = Forall "P#" (p `Or` p')

formula6 = (Exists "P" p) `And` p
pnfFormula6 = Exists "P#" (p' `And` p)

formula7 = p `And` (Exists "P" p)
pnfFormula7 = Exists "P#" (p `And` p')

formula8 = (Exists "P" p) `Or` p
pnfFormula8 = Exists "P#" (p' `Or` p)

formula9 = p `Or` (Exists "P" p)
pnfFormula9 = Exists "P#" (p `Or` p')



formula10 = (Forall "P" p) `And` (Forall "Q" q)
pnfFormula10 = Forall "P" (p `And` p)


formula11 = (Exists "P" p) `Or` (Exists "Q" q)
pnfFormula11 = Exists "P" (p `Or` p)


formula12 = (Forall "X"
                     (Atom(R ("P", [Var "X"]))) 
                     `Or`
                      Atom(R ("R", [Var "Y"]))
        )
        `Imp`
        (Exists "Y"( 
            Exists "Z"(
                    (Atom(R ("Q", [Var "Y"])))
                    `Or`
                    (Not
                        (Exists "Z" (
                            Atom(R ("P", [Var "Z"]))
                            `And`
                            Atom(R ("Q", [Var "Z"]))
                        ))
                    )
                )
        ))


simplifiedFormula12 = 
                        Exists "X"(
                            Forall "Z#"
                                (
                                    (
                                        (Not (Atom(R ("P", [Var "X"]))))
                                        `And`
                                        (Not (Atom(R ("R", [Var "Y"]))))
                                    )
                                    `Or`(
                                        Atom(R ("Q", [Var "X"]))
                                        `Or`(
                                            (Not (Atom(R ("P", [Var "Z#"]))))
                                            `Or`
                                            (Not (Atom(R ("Q", [Var "Z#"]))))
                                            )
                                    )
                                )
                        )

test1 = prenex formula1 == pnfFormula1
test2 = prenex formula2 == pnfFormula2
test3 = prenex formula3 == pnfFormula3
test4 = prenex formula4 == pnfFormula4 
test5 = prenex formula5 == pnfFormula5
test6 = prenex formula6 == pnfFormula6
test7 = prenex formula7 == pnfFormula7
test8 = prenex formula8 == pnfFormula8
test9 = prenex formula9 == pnfFormula9
test10 = prenex formula10 == pnfFormula10

test11 = prenex formula11 == pnfFormula11

test12 = prenex (nnf (folSimplify formula12)) == simplifiedFormula12



runPrenexTests =    "\n Running Prenex Tests: " ++ 
                    "\n Test 1: " ++  show test1 ++
                    "\n Test 2: " ++  show test2 ++
                    "\n Test 3: " ++  show test3 ++
                    "\n Test 4: " ++  show test4 ++
                    "\n Test 5: " ++  show test5 ++
                    "\n Test 6: " ++  show test6 ++
                    "\n Test 7: " ++  show test7 ++
                    "\n Test 8: " ++  show test8 ++
                    "\n Test 9: " ++  show test9 ++
                    "\n Test 10: " ++  show test10 ++
                    "\n Test 11: " ++  show test11 ++
                    "\n Test 12: " ++  show test12 ++
                    "\n"