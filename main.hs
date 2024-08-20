
import FOL
import Simplification

t1 =  Fn("Times", [Var "2", (Fn ("Subtract", [Var "98", Var "98"])  )    ])

t2 = Fn("PI", [])

predi = R ("<", [t1,t2])

formula = (  (Atom predi) `And` (Atom( R ("P",[Var "L"])) )  )

test = Forall "X" 
            (
                Forall "X#" 
                    
                        (Imp
                            (Atom (R ("=",[Var "X", Var "Y"]) ))
                            (Atom (R ("=",[Var "X", Var "X#"]) ))
                        )
                    
            )

sub (Var "Y") =Var "X"
sub p = p



simp = FTrue `Imp` (   Atom(R ("P",[])) `Iff`  ( Atom(R ("P",[])) `Iff` FFalse )   )


simp2 = 
    -- Exists "X" 
            -- (Exists "Y"
                (Exists "Z"
                        -- (
                        --     Atom(R ("P",[Var "X"])) 
                        --     `Imp`
                         (   Atom(R ("Q",[Var "Z"]))  )
                        -- )
                        `Imp`
                        FFalse
                )
            -- )
main = print( folSimplify simp2 )