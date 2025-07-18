module Main where



import FOL
import Simplification




f :: Formula
f = Forall "X" 
            (Forall "Y"
                        (
                            (
                                   Atom(R ("P",[Var "X"])) 
                                    `Or`
                                    
                                (
                                    Atom(R ("P",[Var "Y"])) 
                                    `And`
                                    FFalse
                                )

                            )
                            `Imp`

                            Exists "Z"        (Atom(R ("Q",[])) )

                        )
                
            )


main :: IO ()
main = print( folSimplify f )