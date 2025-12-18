module SubstitutionTests where


import FOL
import Simplification
import Substitution
import Substitution (formulaSubstituition, getVariant)


variantTest1 = getVariant "X" ["Y", "Z"] == "X"
variantTest2 = getVariant "X" ["X", "Y"] == "X#"
variantTest3 = getVariant "X" ["X", "X#"] == "X##"


formula1 = Forall "X"
            (
                Atom(R("=", [Var "X", Var "Y"]))
            )

subFormula1 = Forall "X#"
            (
                Atom(R("=", [Var "X#", Var "X"]))
            )


formula2 = Forall "X" 
            (
                Forall "X#" 
                    
                        (Imp
                            (Atom (R ("=",[Var "X", Var "Y"]) ))
                            (Atom (R ("=",[Var "X", Var "X#"]) ))
                        )
                    
            )

subFormula2 = Forall "X#" 
            (
                Forall "X##" 
                    
                        (Imp
                            (Atom (R ("=",[Var "X#", Var "X"]) ))
                            (Atom (R ("=",[Var "X#", Var "X##"]) ))
                        )
                    
            )

sub (Var "Y") = Var "X"
sub p = p


test1 = formulaSubstituition sub formula1 == subFormula1
test2 = formulaSubstituition sub formula2 == subFormula2

runSubstitutionTests =  "\n Running Substitution Tests \n" ++
                        "\n Variant Test 1: " ++ show variantTest1 ++
                        "\n Variant Test 2: " ++ show variantTest2 ++
                        "\n Variant Test 3: " ++ show variantTest3 ++
                        "\n\n Test 1: " ++ show test1 ++
                        "\n Test 2: " ++ show test2 ++
                        "\n"