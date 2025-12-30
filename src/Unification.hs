{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Unification (
    termContainsVar,
    formulaContainsVar,
    unifyTerms,
    subInList,
    standardiseApart,
    Sub,
    unifyPredicates,
    unify,
    applySubToClause,
    applySubToLiteral,
    applySubToTerms,
    unifyingPairs
    ) where

import qualified Data.Set as Set
import qualified Data.Map as Map

import FOL
    ( Formula(Forall, Atom, Not, And, Or, Imp, Iff, Exists),
      Predicate(R),
      Term(..), Literal (..) )
import Substitution
    ( formulaSubstituition, freeVariablesInFormula, getVariant, termSubstituition )
import Utils (transitiveClosure, literalToPredicate)

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

unifyPredicates :: Predicate -> Predicate -> Maybe Sub
unifyPredicates (R(p, terms1)) (R(q, terms2)) =
    if p == q && length terms1 == length terms2
        then unifyTerms (zip terms1 terms2) Map.empty
        else Nothing

-- Finds the most general unifier between two literals  
-- Applies the transitive closure on the mapping that is returned 
unify :: Predicate -> Predicate -> Maybe Sub
unify p q =
    case sub of
        Just mapping -> Just (transitiveClosure mapping)
        Nothing -> Nothing
    where sub = unifyPredicates p q


-- Applies a substitution to every literal in a clause 
applySubToClause :: Sub -> [Literal] -> [Literal]
applySubToClause _ [] = []
applySubToClause sub ((Pos (R(p, terms))):xs) =
        Pos (R (p, subbedTerms)) : applySubToClause sub xs
        where subbedTerms = applySubToTerms sub terms

applySubToClause sub ((Neg (R(p, terms))):xs) =
        Neg (R (p, subbedTerms)) : applySubToClause sub xs
        where subbedTerms = applySubToTerms sub terms


-- Applies a substitution to every term in a list of terms 
applySubToTerms :: Sub -> [Term] -> [Term]
applySubToTerms _ [] = []
applySubToTerms sub (x:xs) =
    case x of 
        Fn(f, terms) -> Fn(f, applySubToTerms sub terms) : applySubToTerms sub xs 
        _ -> case mapping of 
            Just t -> t : applySubToTerms sub xs
            Nothing -> x : applySubToTerms sub xs
            where mapping = Map.lookup x sub 

-- Applies a substitution to a literal 
applySubToLiteral :: Sub -> Literal -> Literal
applySubToLiteral sub literal = case literal of
    Pos(R(p, terms)) -> Pos (R (p, applySubToTerms sub terms))
    Neg(R(p, terms)) -> Neg (R (p, applySubToTerms sub terms))

-- Given a list of pairs of literals 
-- Returns all pairs that unify along with the unifying substitution
unifyingPairs :: [(Literal, Literal)] -> [(Literal,Literal, Sub)]
unifyingPairs [] = []
unifyingPairs ((a,b): xs) =
    case sub of
        Just s -> (a,b,s) : unifyingPairs xs
        Nothing -> unifyingPairs xs
    where sub = unify (literalToPredicate a) (literalToPredicate b)
