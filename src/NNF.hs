module NNF where 

import FOL ( Formula(Not, Imp, Iff, And, Or, Exists, Forall) )  

nnf :: Formula -> Formula

nnf (p `And` q) = nnf p `And` nnf q
nnf (p `Or` q) = nnf p `Or` nnf q

-- definition of implies
nnf (p `Imp` q) = nnf (Not p) `Or` nnf q

-- definition of bi-implication
nnf (p `Iff` q) =   (nnf p `And` nnf q)
                    `Or`
                    (nnf(Not p) `And` nnf(Not q))
                        
-- double negation 
nnf (Not(Not p)) = nnf p

-- de morgans law
nnf (Not (p `And` q)) = nnf(Not p) `Or` nnf(Not q)
nnf (Not (p `Or` q)) = nnf(Not p) `And` nnf (Not q)

nnf (Not(p `Imp` q)) = nnf p `And` Not(nnf q)

nnf (Not(p `Iff` q)) =  (nnf p `And` nnf (Not q))
                        `Or` 
                        (nnf (Not p) `And` nnf q) 

nnf (Forall x p) = Forall x (nnf p)
nnf (Exists x p) = Exists x (nnf p)

-- push quantifiers outwards
nnf (Not (Forall x p)) = Exists x (nnf(Not p))
nnf (Not (Exists x p)) = Forall x (nnf(Not p))

nnf p = p