{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Substitution.FormulaSubstitutionTests where 
import FOL
import Substitution


formula1 = Atom(R("P", [Var "X"]))
subFormula1 = Atom(R("P", [Var "Y"]))

formula2 = Atom(R("P", [Var "X"]))
subFormula2 = Atom(R("P", [Fn("F", [Var "Y"])]))

formula3 = Not (Atom(R("P", [Var "X"])))
subFormula3 = Not ( Atom(R("P", [Var "Y"])))

formula4 = Atom(R("P", [Var "X"])) `And` Atom(R("Q", [Var "Z"]))
subFormula4 = Atom(R("P", [Var "Y"])) `And` Atom(R("Q", [Var "Z"]))

formula5 = Atom(R("P", [Var "Z"])) `Or` Atom(R("Q", [Var "X"]))
subFormula5 = Atom(R("P", [Var "Z"])) `Or` Atom(R("Q", [Var "Y"]))

formula6 = Atom(R("P", [Var "X"])) `Imp` Atom(R("Q", [Var "Z"]))
subFormula6 = Atom(R("P", [Fn("F", [Var "Y"])])) `Imp` Atom(R("Q", [Var "Z"]))

formula7 = Atom(R("P", [Var "Z"])) `Iff` Atom(R("Q", [Var "X"]))
subFormula7 = Atom(R("P", [Var "Z"])) `Iff` Atom(R("Q", [Fn("F", [Var "Y"])]))



formula8 = Forall "X" ( Atom(R("=", [Var "X", Var "Y"])) )

subFormula8 = Forall "X#" ( Atom(R("=", [Var "X#", Var "X"])) )


formula9 = Exists "X" 
            (
                Exists "X#" 
                    
                        (Imp
                            (Atom (R ("=",[Var "X", Var "Y"]) ))
                            (Atom (R ("=",[Var "X", Var "X#"]) ))
                        )
                    
            )

subFormula9 = Exists "X#" 
            (
                Exists "X##" 
                        (Imp
                            (Atom (R ("=",[Var "X#", Var "X"]) ))
                            (Atom (R ("=",[Var "X#", Var "X##"]) ))
                        )
            )


sub1 (Var "X") = Var "Y"
sub1 t = t

sub2 (Var "X") = Fn("F", [Var "Y"])
sub2 t = t

sub3 (Var "Y") = Var "X"
sub3 p = p

test1 = formulaSubstituition sub1 formula1 == subFormula1
test2 = formulaSubstituition sub2 formula2 == subFormula2
test3 = formulaSubstituition sub1 formula3 == subFormula3
test4 = formulaSubstituition sub1 formula4 == subFormula4
test5 = formulaSubstituition sub1 formula5 == subFormula5
test6 = formulaSubstituition sub2 formula6 == subFormula6
test7 = formulaSubstituition sub2 formula7 == subFormula7
test8 = formulaSubstituition sub3 formula8 == subFormula8
test9 = formulaSubstituition sub3 formula9 == subFormula9


runFormulaSubstitutionTests = concat 
    [
        "\n\n Running Formula Substitution Tests: ", 
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