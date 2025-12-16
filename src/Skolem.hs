module Skolem where 

import FOL
import qualified Data.Set as Set
import Substitution
import Simplification (folSimplify, nnf)
import Prenex

getFunctionsInTerm :: Term -> Set.Set String
getFunctionsInTerm (Var _) = Set.empty
getFunctionsInTerm (Fn (fn, terms)) = Set.singleton fn `Set.union` Set.unions  (map getFunctionsInTerm terms)

getFunctionsInFormula :: Formula -> Set.Set String
getFunctionsInFormula FFalse =  Set.empty
getFunctionsInFormula FTrue = Set.empty
getFunctionsInFormula (Atom(R(_, terms))) = Set.unions (map getFunctionsInTerm terms)
getFunctionsInFormula (Not p) = getFunctionsInFormula p
getFunctionsInFormula (p `And` q) = getFunctionsInFormula p `Set.union` getFunctionsInFormula q
getFunctionsInFormula (p `Or` q) = getFunctionsInFormula p `Set.union` getFunctionsInFormula q
getFunctionsInFormula (p `Imp` q) = getFunctionsInFormula p `Set.union` getFunctionsInFormula q
getFunctionsInFormula (p `Iff` q) = getFunctionsInFormula p `Set.union` getFunctionsInFormula q
getFunctionsInFormula (Forall x p) = getFunctionsInFormula p
getFunctionsInFormula (Exists x p) = getFunctionsInFormula p 



skolem2 :: (Formula -> Formula -> Formula) -> Formula -> Formula -> [String] -> (Formula, [String])
skolem2 constructor p q funcs = 
    let (p', newFuncs) = skolem p funcs in
    let (q', newFuncs') = skolem q newFuncs in 
        (p' `constructor` q', newFuncs')

skolem :: Formula -> [String] -> (Formula, [String])

skolem (Exists x p) funcs = 
    let freeVars = freeVariablesInFormula (Exists x p) in
    let newFuncName = getVariant "SK" funcs in
    let newFunc = Fn(newFuncName, map Var (Set.toList freeVars)) in
    let newFormula = formulaSubstituition (\a -> if a == Var x then newFunc else a) p in
        skolem newFormula (funcs++[newFuncName])

skolem (Forall x p) funcs = 
    let (newFormula, newFuncs) = skolem p funcs
    in (Forall x newFormula, newFuncs)

skolem (p `And` q) funcs = 
    let constructor x y =  x `And` y in 
        skolem2 constructor p q funcs

skolem (p `Or` q) funcs = 
    let constructor x y = x `Or` y in 
        skolem2 constructor p q funcs

skolem p funcs = (p, funcs) 
    
skolemiser :: Formula -> Formula
skolemiser p = fst (skolem (nnf (folSimplify p)) (Set.toList(getFunctionsInFormula p))) 

removeUniversalQuantifiers :: Formula -> Formula
removeUniversalQuantifiers (Forall _ p)  = removeUniversalQuantifiers p
removeUniversalQuantifiers p = p 

fullSkolemise :: Formula -> Formula
fullSkolemise p = removeUniversalQuantifiers(prenex (skolemiser p))