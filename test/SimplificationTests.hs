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
                            
                        


formula6 = (
            (Exists "Y" (Atom(R ("Q", [Var "Y"]))))
            `Iff`
            (Exists "Z" (Atom(R ("P", [Var "Z"]))))
            )
            
nnfFormula6 =   (
                    (Exists "Y" (Atom(R ("Q", [Var "Y"]))))
                    `And`
                    (Exists "Z" (Atom(R ("P", [Var "Z"]))))
                )
                `Or`
                (

                    (Forall "Y" (Not(Atom(R ("Q", [Var "Y"])))))
                    `And`
                    (Forall "Z" (Not(Atom(R ("P", [Var "Z"])))))
                )


formula7 = (
                (Exists "Y" (Atom(R ("Q", [Var "Y"]))))
                `Iff`
                (Exists "Z" (Atom(R ("P", [Var "Z"]))))
            )
            `And`
            Atom(R ("Q", [Var "Z"]))
            

nnfFormula7 =   (
                    (
                        (Exists "Y" (Atom(R ("Q", [Var "Y"]))))
                        `And`
                        (Exists "Z" (Atom(R ("P", [Var "Z"]))))
                    )
                    `Or`
                    (

                        (Forall "Y" (Not(Atom(R ("Q", [Var "Y"])))))
                        `And`
                        (Forall "Z" (Not(Atom(R ("P", [Var "Z"])))))
                    )
                )
                `And`
                Atom(R ("Q", [Var "Z"]))


-- formula_ =   (Forall "X" (Atom(R("P", [Var "X"]))) ) 
--             `Imp`
--             (
                
--                 (Exists "Y" (Atom(R ("Q", [Var "Y"]))))
--                     `Iff`
--                 (    
--                     (Exists "Z" (Atom(R ("P", [Var "Z"]))))
--                     `And`
--                     Atom(R ("Q", [Var "Z"]))
--                 )
--             )


-- nnfFormula_ =   (Exists "X" (Not (Atom(R ("P", [Var "X"]))))) `Or`
--                 (
--                     (Exists "Y" (Atom(R ("Q", [Var "Y"]))) ) `And`
--                     (Exists "Z" (Atom(R ("P", [Var "Z"]))))  `And`
--                     Atom(R ("Q", [Var "Z"]))
--                 ) `Or`
--                 (
--                     (Forall "Y" (Not (Atom(R ("Q", [Var "Y"]))))) `And`
--                     (Forall "Z" (Not (Atom(R ("P", [Var "Z"])))))
--                 ) `Or`
--                 ((Atom(R ("Q", [Var "Z"]))))

             
    
test1 = propSimplify formula1 == formula1
test2 = propSimplify formula2 == simplifiedFormula2
test3 = folSimplify formula3 == simplifiedFormula3
test4 = propSimplify (folSimplify formula4) == simplifiedFormula4
test5 = propSimplify (folSimplify formula5) == simplifiedFormula5
test6 = nnf formula6 == nnfFormula6
test7 = nnf formula7 == nnfFormula7


runSimplificationTests :: [Char]
runSimplificationTests =    "\n Running Simplification Tests \n" ++
                            "\n Test 1: " ++ show test1 ++ 
                            "\n Test 2: " ++ show test2 ++
                            "\n Test 3: " ++ show test3 ++
                            "\n Test 4: " ++ show test4 ++
                            "\n Test 5: " ++ show test5 ++
                            "\n Test 6: " ++ show test6 ++
                            "\n Test 7: " ++ show test7 ++
                            "\n"












