module Prenex (prenex) where 

import FOL
import Substitution

prenex :: Formula -> Formula
prenex (Forall x formula) = Forall x (prenex formula)
prenex (Exists x formula) = Exists x (prenex formula)
prenex (p `And` q) = pullQuantifiers (prenex p  `And` prenex q)
prenex (p `Or` q) = pullQuantifiers (prenex p  `Or` prenex q)
prenex p = p


pullQuantifiers :: Formula -> Formula 
pullQuantifiers formula =   case formula of 
                            (Forall x p) `And` (Forall y q) -> pullQ True True formula makeForall makeAnd x y p q
                            (Exists x p) `Or` (Exists y q)  -> pullQ True True formula makeExists makeOr x y p q

                            (Forall x p) `And` q -> pullQ True False formula makeForall makeAnd x x p q
                            p `And` (Forall x q) -> pullQ False True formula makeForall makeAnd x x p q

                            (Forall x p) `Or` q -> pullQ True False formula makeForall makeOr x x p q
                            p `Or` (Forall x q) -> pullQ False True formula makeForall makeOr x x p q

                            (Exists x p) `And` q -> pullQ True False formula makeExists makeAnd x x p q
                            p `And` (Exists x q) -> pullQ False True formula makeExists makeAnd x x p q

                            (Exists x p) `Or` q -> pullQ True False formula makeExists makeOr x x p q
                            p `Or` (Exists x q) -> pullQ False True formula makeExists makeOr x x p q

                            _ -> formula 

pullQ :: Bool -> Bool -> Formula -> ([Char] -> Formula -> t) -> (Formula -> Formula -> Formula) -> [Char] -> [Char] -> Formula -> Formula -> t
pullQ left right formula quantifier operation x y p q = 
    let z = getVariant x (freeVariablesInFormula formula) in 
    let p' = if left then formulaSubstituition (\a -> if Var x == a then Var z else a) p else p in 
    let q' = if right then formulaSubstituition (\a -> if Var y == a then Var z else a) q else q in 
    quantifier z (pullQuantifiers(operation p' q'))
