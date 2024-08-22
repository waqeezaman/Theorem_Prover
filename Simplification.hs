module Simplification where 


import FOL



propTautology (Not FTrue) = FFalse
propTautology (Not FFalse) = FTrue

propTautology (Not (Not p)) = p

propTautology (p `And` FFalse) = FFalse
propTautology (FFalse `And` p) = FFalse

propTautology (p `And` FTrue) = p
propTautology (FTrue `And` p) = p

propTautology (p `Or` FFalse) = p
propTautology (FFalse `Or` p) = p

propTautology (p `Or` FTrue) = FTrue
propTautology (FTrue `Or` p) = FTrue

propTautology (FFalse `Imp` p) = FTrue
propTautology (p `Imp` FTrue) = FTrue

propTautology (p `Imp` FFalse) = Not p
propTautology (FTrue `Imp` p) = p

propTautology (FTrue `Iff` p) = p
propTautology (p `Iff` FTrue) = p

propTautology (FFalse `Iff` p) = Not p
propTautology (p `Iff` FFalse) = Not p

propTautology other = other 



-- propSimplify FFalse = FFalse
-- propSimplify FTrue = FTrue
-- propSimplify (Atom (R(pred, args))) = Atom (R(pred, args)) 

propSimplify (Not p) = propTautology (Not (propSimplify p))
propSimplify (p `And` q) = propTautology ( propSimplify p `And` propSimplify q)
propSimplify (p `Or` q) = propTautology (  propSimplify p `Or`  propSimplify q)
propSimplify (p `Imp` q) = propTautology ( propSimplify p `Imp` propSimplify q)
propSimplify (p `Iff` q) = propTautology ( propSimplify p `Iff` propSimplify q)

propSimplify p = p 


folSimplify1 (Forall x p) = if x `elem` freeVariablesInFormula p then 
                                Forall x p
                            else
                                p
folSimplify1 (Exists x p) = if x `elem` freeVariablesInFormula p then 
                                Exists x p
                            else
                                p
                                
folSimplify1 p = propSimplify p



folSimplify (Not p) = folSimplify1( Not (folSimplify p) )

folSimplify (p `And` q) = folSimplify1( folSimplify p `And` folSimplify q)
folSimplify (p `Or` q) = folSimplify1( folSimplify p `Or` folSimplify q)

folSimplify (p `Imp` q) = folSimplify1( folSimplify p `Imp` folSimplify q)
folSimplify (p `Iff` q) = folSimplify1( folSimplify p `Iff` folSimplify q)

folSimplify (Forall x p) = folSimplify1( Forall x (folSimplify p) )
folSimplify (Exists x p) = folSimplify1( Exists x (folSimplify p) )
folSimplify p = p













-- propositionalSimplification (Not (p `And` q) ) = Not p `Or` Not q
-- propositionalSimplification (Not (p `Or` q) ) = Not p `And` Not q

-- propositionalSimplification (p `Imp` q) = Not p `Or` q
-- propositionalSimplification (p `Iff` q) = p `Imp` q `And` q `Imp` p 

