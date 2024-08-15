
import FOL

t1 =  Fn("Times", [Var "2", (Fn ("Subtract", [Var "98", Var "98"])  )    ])

t2 = Fn("PI", [])

predi = R ("<", [t1,t2])


main = print( freeVariablesInTerm t1)