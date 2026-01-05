module Substitution (
    generalise,
    termSubstituition,
    freeVariablesInTerm, 
    freeVariablesInFormula,
    formulaSubstituition,
    getVariant
    ) where 

import FOL ( Formula(..), Predicate(R), Term(..) )
import Data.Set (Set)
import qualified Data.Set as Set

-- Returns a set contaning all the variables in a term 
freeVariablesInTerm :: Term -> Set String
freeVariablesInTerm (Var x) = Set.singleton x
freeVariablesInTerm (Fn (_, args)) =  Set.unions (map freeVariablesInTerm args)
    
-- Returns a set containing all the variables that occur freely in the formula
freeVariablesInFormula :: Formula -> Set String
freeVariablesInFormula FFalse = Set.empty
freeVariablesInFormula FTrue = Set.empty
freeVariablesInFormula  (Atom (R  (p ,args ) )) = Set.unions( map freeVariablesInTerm args)
freeVariablesInFormula  (Not p) = freeVariablesInFormula p
freeVariablesInFormula  (And p q) =  freeVariablesInFormula p `Set.union` freeVariablesInFormula q
freeVariablesInFormula  (Or p q ) =  freeVariablesInFormula p `Set.union` freeVariablesInFormula q
freeVariablesInFormula  (Imp p q) =  freeVariablesInFormula p `Set.union` freeVariablesInFormula q
freeVariablesInFormula  (Iff p q) =  freeVariablesInFormula p `Set.union` freeVariablesInFormula q

freeVariablesInFormula  (Forall x p) = Set.delete x (freeVariablesInFormula p)
freeVariablesInFormula  (Exists x p) = Set.delete x (freeVariablesInFormula p)


generalise :: Formula -> Formula
generalise formula =   foldr Forall formula   (Set.elems (freeVariablesInFormula formula))   


termSubstituition :: (Term -> Term) -> Term -> Term
termSubstituition subfunc (Var x) = subfunc (Var x)
termSubstituition subfunc (Fn (func , args)) = Fn (func ,  map (termSubstituition subfunc) args  )


getVariant :: Foldable t => String -> t String -> String
getVariant x vars = if x `elem`  vars then getVariant (x++"#") vars 
                    else x 


formulaSubstituition :: (Term -> Term) -> Formula -> Formula
formulaSubstituition _ FFalse = FFalse
formulaSubstituition _ FTrue = FTrue

formulaSubstituition subfunc (Atom(R(pred, args ))) =   Atom(R(pred, map (termSubstituition subfunc) args ))

formulaSubstituition subfunc (Not p) = Not (formulaSubstituition subfunc p)

formulaSubstituition subfunc (And p q) = formulaSubstituition subfunc p 
                                        `And`
                                        formulaSubstituition subfunc q

formulaSubstituition subfunc (Or p q) = formulaSubstituition subfunc p 
                                        `Or`
                                        formulaSubstituition subfunc q

formulaSubstituition subfunc (Imp p q) = formulaSubstituition subfunc p 
                                        `Imp`
                                        formulaSubstituition subfunc q

formulaSubstituition subfunc (Iff p q) = formulaSubstituition subfunc p 
                                        `Iff`
                                        formulaSubstituition subfunc q

formulaSubstituition subfunc (Forall x formula) = quantifierSubstituition subfunc (Forall x formula)
formulaSubstituition subfunc (Exists x formula) = quantifierSubstituition subfunc (Exists x formula)


varString :: Term -> String
varString (Var x ) = x
varString _ = error "Attempting to get the variable string of a function term"

-- We need a different procedure for substituting into Formulas with a quantifier 
-- This is to avoid variable capture 
-- E.g Given 
-- Exists X. P(X, Y)
-- and the substitution Y -> X
-- Naively applying this would give us 
-- Exists X. P(X, X) , this is incorrect as Y was not previously quantified
-- We say that the variable has been captured 
-- To avoid this we rename quantified variables to a unique variable name 
-- This gives us:
--  Exists X#. P(X#, X)
quantifierSubstituition :: (Term -> Term) -> Formula -> Formula

quantifierSubstituition subfunc (Forall var pred) = 
    let subfunc'  =  if var `elem` freeVariablesInFormula pred then 
                        (\x -> if x == Var var then 
                                    Var (getVariant var (freeVariablesInFormula pred))
                                else
                                    subfunc x
                        )
                    else  
                        subfunc     
    in Forall (varString(subfunc' (Var var) )) (formulaSubstituition subfunc' pred) 

quantifierSubstituition subfunc (Exists var pred) = 
    let subfunc'  =  if var `elem` freeVariablesInFormula pred then 
                        (\x -> if x == Var var then 
                                    Var (getVariant var (freeVariablesInFormula pred))
                                else
                                    subfunc x
                        )
                    else  
                        subfunc     
    in Exists (varString(subfunc' (Var var) )) (formulaSubstituition subfunc' pred) 

quantifierSubstituition _ f = f