module Substitution where 

import FOL
-- import Data.Set 
import Data.List (union, delete)

import Data.Set (Set)
import qualified Data.Set as Set



freeVariablesInTerm (Var x) = Set.singleton x
freeVariablesInTerm (Fn (func, args)) =  Set.unions (map freeVariablesInTerm args)
    



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



generalise formula =   foldr Forall formula   (Set.elems (freeVariablesInFormula formula))   


termSubstituition subfunc (Var x) = subfunc (Var x)
termSubstituition subfunc (Fn (func , args)) = Fn (func ,  map subfunc args  )


getVariant x vars = if x `elem`  vars then getVariant (x++"#") vars 
                    else x 




formulaSubstituition subfunc FFalse = FFalse
formulaSubstituition subfunc FTrue = FTrue

formulaSubstituition subfunc (Atom(R(pred, args ))) =   Atom(R(pred, map (termSubstituition subfunc) args ))

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



varString (Var x ) = x



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
