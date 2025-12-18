module Simplification where 

import FOL
import Substitution

propTautology :: Formula -> Formula

propTautology (Not FTrue) = FFalse
propTautology (Not FFalse) = FTrue

propTautology (Not (Not p)) = p

propTautology (_ `And` FFalse) = FFalse
propTautology (FFalse `And` _) = FFalse

propTautology (p `And` FTrue) = p
propTautology (FTrue `And` p) = p

propTautology (p `Or` FFalse) = p
propTautology (FFalse `Or` p) = p

propTautology (_ `Or` FTrue) = FTrue
propTautology (FTrue `Or` _) = FTrue

propTautology (FFalse `Imp` _) = FTrue
propTautology (_ `Imp` FTrue) = FTrue

propTautology (p `Imp` FFalse) = Not p
propTautology (FTrue `Imp` p) = p

propTautology (FTrue `Iff` p) = p
propTautology (p `Iff` FTrue) = p

propTautology (FFalse `Iff` p) = Not p
propTautology (p `Iff` FFalse) = Not p

propTautology other = other 


propSimplify :: Formula -> Formula

propSimplify (Not p) = propTautology (Not (propSimplify p))
propSimplify (p `And` q) = propTautology ( propSimplify p `And` propSimplify q)
propSimplify (p `Or` q) = propTautology (  propSimplify p `Or`  propSimplify q)
propSimplify (p `Imp` q) = propTautology ( propSimplify p `Imp` propSimplify q)
propSimplify (p `Iff` q) = propTautology ( propSimplify p `Iff` propSimplify q)
propSimplify p = p 


-- Removes redundant quantifiers in a formula 
folSimplify1 :: Formula -> Formula

folSimplify1 (Forall x p) = if x `elem` freeVariablesInFormula p then 
                                Forall x p
                            else
                                p
folSimplify1 (Exists x p) = if x `elem` freeVariablesInFormula p then 
                                Exists x p
                            else
                                p
                                
folSimplify1 p = propSimplify p



folSimplify :: Formula -> Formula

folSimplify (Not p) = folSimplify1( Not (folSimplify p) )

folSimplify (p `And` q) = folSimplify1( folSimplify p `And` folSimplify q)
folSimplify (p `Or` q) = folSimplify1( folSimplify p `Or` folSimplify q)

folSimplify (p `Imp` q) = folSimplify1( folSimplify p `Imp` folSimplify q)
folSimplify (p `Iff` q) = folSimplify1( folSimplify p `Iff` folSimplify q)

folSimplify (Forall x p) = folSimplify1( Forall x (folSimplify p) )
folSimplify (Exists x p) = folSimplify1( Exists x (folSimplify p) )
folSimplify p = p