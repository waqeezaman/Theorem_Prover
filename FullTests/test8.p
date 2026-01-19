% Status: Satisfiable

cnf(f1,hypothesis,
    ( p(X)
    | p(a)
     )).

cnf(f2,negated_conjecture,
    ( p(X) 
    | ~p(a)
    )).
    