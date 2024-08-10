data Term = Var String | Fn (String , [Term] ) deriving (Eq,Show)

data Predicate = R (String, [Term]) deriving (Eq, Show)



-- termval (domain, functions, predicates ) v (Var x) = v x

-- termval (domain, functions, predicates) v (Fn (func ,terms)) = functions func 



-- define holds


t1 =  Fn("Times", [Var "2", (Fn ("Subtract", [Var "98", Var "P"])  )    ])



t2 = Fn("PI", [])



predi = R ("<", [t1,t2])


main = print predi