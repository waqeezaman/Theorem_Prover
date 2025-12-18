module SkolemTests where

import FOL
import Skolem
import Simplification
import NNF

formula1 = Exists "X" (Atom((R("P", [Var "X"]))))
skolemFormula1 = Atom((R("P", [Fn ("SK", [])])))

formula2 = Forall "X"
            (
                Exists "Y"
                (
                    Atom((R("P", [Var "X", Var "Y"])))
                )
            )

skolemFormula2 = Atom((R("P", [Var "X", Fn("SK", [Var "X"])])))

formula3 =
     Exists "X" 
            (
                Forall "Y" 
                (
                    Atom(R("P", [Var "X", Var "Y"]))
                )
            )

skolemFormula3 = Atom(R("P", [Fn("SK", []), Var "Y#"]))

formula4 = Exists "Y"
            (
                Atom(R("LessThan", [Var "X", Var "Y"]))
                `Imp`
                (
                    Forall "U" 
                    (
                        Exists "V"
                        (
                            Atom(R("LessThan", [
                                Fn("Times", [Var "X", Var "U"]),
                                Fn("Times", [Var "Y", Var "V"])
                            ]))
                        )
                    )
                )
            )

skolemFormula4 = Not(
    Atom(R("LessThan", [Var "X", Fn("SK", [Var "X"])])) 
    )
    `Or`
    Atom(R("LessThan", [
        Fn("Times", [Var "X", Var "U#"]),
        Fn("Times", [Fn("SK", [Var "X"]),Fn("SK#", [Var "U#", Var "X"]) ])
    ]))


formula5 = Forall "X"
            (
                Atom(R("P", [Var "X"]))
                `Imp`
                (
                    Exists "Y"
                    (
                        Exists "Z"
                        (
                            Atom(R("Q", [Var "Y"]))
                            `Or`
                            Not(
                                Exists "Z"
                                (
                                    Atom(R("P", [Var "Z"]))
                                    `And`
                                    Atom(R("Q", [Var "Z"]))
                                )
                            )   
                        )
                    )
                )
            )

skolemFormula5 =    (Not (Atom(R("P", [Var "X"]))))
                    `Or`
                    (
                        (Atom(R("Q", [Fn("SK", [])])))
                        `Or`
                        (
                            (Not (Atom(R("P", [Var "Z#"]))))
                            `Or`
                            (Not (Atom(R("Q", [Var "Z#"] ))))
                        )
                    )


test1 = skolemFormula1 == fullSkolemise formula1
test2 = skolemFormula2 == fullSkolemise formula2
test3 = skolemFormula3 == fullSkolemise formula3
test4 = skolemFormula4 == fullSkolemise formula4
test5 = skolemFormula5 == fullSkolemise formula5

runSkolemTests = "\n Skolem Test Results"
    ++ "\n Test 1: " ++ show test1
    ++ "\n Test 2: " ++ show test2
    ++ "\n Test 3: " ++ show test3
    ++ "\n Test 4: " ++ show test4
    ++ "\n Test 5: " ++ show test5 