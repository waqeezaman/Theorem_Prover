data Term = Var String | Fn (String , [Term] ) deriving (Eq,Show)

data Predicate = R (String, [Term])  deriving (Eq, Show)

data Formula = FFalse | FTrue | Atom Predicate | Not Formula 
                | And Formula Formula | Or Formula Formula 
                | Imp Formula Formula | Iff Formula Formula
                | Forall  Term Formula | Exists Term Formula 



-- termval :: ([a], String->[Term]->Term , String-> [Term] -> Bool) -> (Term -> Term) -> Term -> Term

termval (domain, functions, predicates ) v (Var x) = v (Var x)

termval (domain, functions, predicates) v (Fn (func ,terms)) = 
    functions func ( map (termval (domain, functions,predicates) v) terms) 


holds (domain, functions, predicates) v FFalse = False
holds (domain, functions, predicates) v FTrue = True
holds (domain, functions, predicates) v (Atom(R(pred, terms))) = 
    predicates pred (map (termval (domain, functions, predicates) v) terms)

holds (domain, functions, predicates) v (Not p) = 
    not (holds (domain, functions, predicates) v p )

holds (domain, functions, predicates) v (And p q) = 
    holds (domain, functions, predicates) v p  &&
    holds (domain, functions, predicates) v q 

holds (domain, functions, predicates) v (Or p q) = 
    holds (domain, functions, predicates) v p  ||
    holds (domain, functions, predicates) v q 

holds (domain, functions, predicates) v (Imp p q) = 
    not (holds (domain, functions, predicates) v p ) ||
    holds (domain, functions, predicates) v q 

holds (domain, functions, predicates) v (Iff p q) = 
    holds (domain, functions, predicates) v p ==
    holds (domain, functions, predicates) v q 

holds (domain, functions, predicates) v (Forall p q) = 
   all  (\a -> let x = a in  holds (domain, functions, predicates ) 
                            (\x -> if x == p then a else v x) q
        )
    
   domain

holds (domain, functions, predicates) v (Exists p q) = 
   any  (\a -> let x = a in  holds (domain, functions, predicates ) 
                            (\x -> if x == p then a else v x) q
        )
    
   domain



t1 =  Fn("Times", [Var "2", (Fn ("Subtract", [Var "98", Var "P"])  )    ])

t2 = Fn("PI", [])

predi = R ("<", [t1,t2])


main = print predi