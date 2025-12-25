{-# OPTIONS_GHC -Wno-missing-signatures #-}
module NNFTests where

import FOL
import NNF

formula1 = Exists "Y" (Atom (R ("Q", [Var "Y"])))
            `Iff`
            Exists "Z" (Atom (R ("P", [Var "Z"])))

nnfFormula1 =   (
                    Exists "Y" (Atom (R ("Q", [Var "Y"])))
                    `And`
                    Exists "Z" (Atom (R ("P", [Var "Z"])))
                )
                `Or`
                (

                    Forall "Y" (Not (Atom (R ("Q", [Var "Y"]))))
                    `And`
                    Forall "Z" (Not (Atom (R ("P", [Var "Z"]))))
                )

formula2 = (
                Exists "Y" (Atom (R ("Q", [Var "Y"])))
                `Iff`
                Exists "Z" (Atom (R ("P", [Var "Z"])))
            )
            `And`
            Atom (R ("Q", [Var "Z"]))


nnfFormula2 =   (
                    (
                        Exists "Y" (Atom (R ("Q", [Var "Y"])))
                        `And`
                        Exists "Z" (Atom (R ("P", [Var "Z"])))
                    )
                    `Or`
                    (
                        Forall "Y" (Not (Atom (R ("Q", [Var "Y"]))))
                        `And`
                        Forall "Z" (Not (Atom (R ("P", [Var "Z"]))))
                    )
                )
                `And`
                Atom (R ("Q", [Var "Z"]))

test1 = nnf formula1 == nnfFormula1
test2 = nnf formula2 == nnfFormula2

runNNFTests = concat 
    [
        "\n\n Running NNF Tests ",
        "\n Test 1: " ++ show test1,    
        "\n Test 2: " ++ show test2
    ]