{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Unification (
    termContainsVar,
    formulaContainsVar,
    unifyTerms,
    subInList,
    standardiseApart,
    Sub,
    unifyAtoms,
    unify
    ) where

import qualified Data.Set as Set
import qualified Data.Map as Map

import FOL
    ( Formula(Forall, Atom, Not, And, Or, Imp, Iff, Exists),
      Predicate(R),
      Term(..) )
import Substitution
    ( formulaSubstituition, freeVariablesInFormula, getVariant, termSubstituition )
import Utils (transitiveClosure)

type Sub = Map.Map Term Term

termContainsVar :: String -> Term -> Bool
termContainsVar var (Var x) = x == var
termContainsVar var (Fn(_, terms)) =  any (termContainsVar var) terms

formulaContainsVar :: String -> Formula -> Bool
formulaContainsVar var formula = case formula of
    Atom(R(_, terms)) -> any (termContainsVar var) terms
    Not p -> formulaContainsVar var p
    p `And` q -> eitherContains p q
    p `Or` q -> eitherContains p q
    p `Imp` q -> eitherContains p q
    p `Iff` q -> eitherContains p q
    Exists _ p -> formulaContainsVar var p
    Forall _ p -> formulaContainsVar var p
    _ -> False
    where
        eitherContains p q = formulaContainsVar var p || formulaContainsVar var q

-- Function to standardise apart two formulas 
-- If these two formulas share any variable names then 
-- Renames all variable names in the second formula to unique variable names 
-- Neccesary to do before unification
standardiseApart :: Formula -> Formula -> Formula
standardiseApart p q =
    standardise common allVars q
    where
        pVars = freeVariablesInFormula p
        qVars = freeVariablesInFormula q
        allVars = Set.toList (pVars `Set.union` qVars)
        common = Set.toList (qVars `Set.intersection` pVars)

standardise :: [String] -> [String] -> Formula -> Formula
standardise [] _ p = p
standardise (x:xs) allVars p =
    standardise xs newVars newFormula
    where
        newFormula = formulaSubstituition subFunc p
        newVar = getVariant x allVars
        newVars = allVars ++ [newVar]
        subFunc a = if Var x == a then Var newVar else a

-- Takes two terms and substitues one term in for another 
-- Substitutes the second term for every occurence of the second term 
-- In the list of pairs of terms 
subInList :: Term -> Term -> [(Term,Term)] -> [(Term, Term)]
subInList _ _ [] = []
subInList s t ((a,b):rest) =
    (termSubstituition subFunc a, termSubstituition subFunc b) : subInList s t rest
    where subFunc x = if x == s then t else x

-- Unify a list of term pairs 
-- Takes in a list of term pairs to unify 
-- The current substitution function 
-- Returns a potential unification of the terms    
unifyTerms :: [(Term, Term)] -> Sub -> Maybe Sub
unifyTerms [] sub = Just sub
unifyTerms ((a,b): rest) sub = case (a,b) of

    -- Delete Rule
    -- The two terms are identical
    -- therefore they can be removed  
    _ | a == b -> unifyTerms rest sub

    -- Eliminate Rule 
    -- If x does not occur in t 
    -- replace x with t in all term pairs yet to be resolved 
    -- add x -> t to the substitution
    (Var x, t) ->   if termContainsVar x t then
                        Nothing
                    else
                        unifyTerms newRest newSub
                        where
                            newRest = subInList (Var x) t rest
                            newSub = Map.insert (Var x) t subKeys
                            subKeys = Map.mapKeys (termSubstituition subFunc) subValues
                            subValues = Map.map (termSubstituition subFunc) sub
                            subFunc a = if a == Var x then t else a


    -- Swap Rule 
    (t, Var x) -> unifyTerms ((Var x, t): rest) sub

    -- Decompose Rule
    -- If f and g are the same function, then unify sub terms
    -- otherwise no possible unification exists  
    (Fn (f, args1), Fn (g, args2)) ->
        if f == g && length args1 == length args2
            then unifyTerms (zip args1 args2 ++ rest) sub
            else Nothing


unifyAtoms :: Formula -> Formula -> Maybe Sub
unifyAtoms (Atom (R(p, terms1))) (Atom (R(p2, terms2))) =
    if p == p2 && length terms1 == length terms2
        then unifyTerms (zip terms1 terms2) Map.empty
        else Nothing
unifyAtoms _ _ = error "unifyAtoms can only take in atoms as input"


-- Calls unifyAtoms on two atoms 
-- Applies the transitive closure on the mapping that is returned 
unify :: Formula -> Formula -> Maybe Sub
unify (Atom (R(p, terms1))) (Atom (R(p2, terms2))) =
    case sub of
        Just mapping -> Just (transitiveClosure mapping)
        Nothing -> Nothing
    where sub = unifyAtoms (Atom (R (p, terms1))) (Atom (R (p2, terms2)))
unify _ _ = error "unify can only be applied to atoms"
