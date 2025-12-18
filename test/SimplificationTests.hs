module SimplificationTests where

import FOL
import Simplification
import Simplification ( propSimplify, folSimplify)
import FOL (Formula(Forall), prettyPrintFormula)

t1 =  Fn("Times", [Var "2", (Fn ("Subtract", [Var "98", Var "98"])  )    ])

t2 = Fn("PI", [])

pred1 = R ("<", [t1,t2])

formula1 = (  (Atom pred1) `And` (Atom( R ("P",[Var "L"])) )  )

formula2 = FTrue `Imp` (   Atom(R ("P",[])) `Iff`  ( Atom(R ("P",[])) `Iff` FFalse )   )
simplifiedFormula2 =     Atom(R ("P",[])) `Iff` Not (Atom(R ("P",[])))    

formula3 = 
    Forall "X" 
            (Forall "Y"
                (Forall "Z"
                        (
                                Atom(R ("P",[Var "X"])) 
                                `Imp`
                                Atom(R ("Q",[Var "Z"]))    
                        )
                        
                )    
            )

simplifiedFormula3 = Forall "X"
                        (Forall "Z"
                                (
                                        Atom(R ("P",[Var "X"])) 
                                        `Imp`
                                        Atom(R ("Q",[Var "Z"]))    
                                )
                                
                        )   
                    

formula4 = 
    Forall "X" 
            (Forall "Y"
                (Forall "Z"
                        (
                            (
                                Atom(R ("P",[Var "X"])) 
                                `Imp`
                                Atom(R ("Q",[Var "Z"]))  
                            )

                            
                            `Imp`
                            
                            FFalse
                        )
                        
                )    
            )
simplifiedFormula4 = Forall "X" 
                        (Forall "Z"   
                            (Not (
                                Atom(R ("P",[Var "X"])) 
                                `Imp`
                                Atom(R ("Q",[Var "Z"]))  
                            ))      
                        )    

formula5 = Forall "X" 
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

simplifiedFormula5 = Forall "X" 
                        (
                            Atom(R ("P",[Var "X"])) 
                            `Imp`
                            Atom(R ("Q",[])) 
                        )
                                         
    
test1 = propSimplify formula1 == formula1
test2 = propSimplify formula2 == simplifiedFormula2
test3 = folSimplify formula3 == simplifiedFormula3
test4 = propSimplify (folSimplify formula4) == simplifiedFormula4
test5 = propSimplify (folSimplify formula5) == simplifiedFormula5

runSimplificationTests :: [Char]
runSimplificationTests =    "\n Running Simplification Tests \n" ++
                            "\n Test 1: " ++ show test1 ++ 
                            "\n Test 2: " ++ show test2 ++
                            "\n Test 3: " ++ show test3 ++
                            "\n Test 4: " ++ show test4 ++
                            "\n Test 5: " ++ show test5 ++
                            "\n"
