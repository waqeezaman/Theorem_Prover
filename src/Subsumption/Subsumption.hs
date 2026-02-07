module Subsumption.Subsumption
    (
        groundClause,
        getVarsInClause,
        isSubsumedBySeenClauses,
        isSubsumedBy,
        canMatch,
        matchLiterals,
        matchPredicates,
        matchTerms,
        matchTerm
    )
    where

import FOL (Clause (..), Literal (..), Predicate (..), Term (..), getLiterals)
import Subsumption.SubsumptionFilter (ClauseTrie, retrieveAllPossiblySubsumingClauses, getFeatureVector)
import qualified Data.Map as Map
import Unification (Sub, applySubToClause)
import Data.List (nub)

-- Given a clause returns a ground version of it 
-- Maps all variable to a "unique" constant 
groundClause :: Clause -> Clause
groundClause clause =
    Clause $ applySubToClause sub $ getLiterals clause
    where
        sub = Map.fromList [(Var v, Fn ("_G_"++v, [])) | v <- variables]
        variables = getVarsInClause clause

-- Returns a list of all the variables in the clause  
getVarsInClause :: Clause -> [String]
getVarsInClause (Clause lits) = nub $ concatMap getVarsInLit lits
  where
    getVarsInLit (Pos (R (_, ts))) = concatMap getVarsInTerm ts
    getVarsInLit (Neg (R (_, ts))) = concatMap getVarsInTerm ts
    getVarsInTerm (Var v) = [v]
    getVarsInTerm (Fn (_, ts)) = concatMap getVarsInTerm ts


-- Returns true if a clause in the trie subsumes the clause C
isSubsumedBySeenClauses :: Clause -> [String] -> ClauseTrie -> Bool
isSubsumedBySeenClauses c ordering trie =
    any (`isSubsumedBy` c) candidateClauses
    where
        featureVector = getFeatureVector c
        candidateClauses = retrieveAllPossiblySubsumingClauses ordering featureVector trie


-- Retruns True if clause C susbumes Clause D
isSubsumedBy :: Clause -> Clause -> Bool
isSubsumedBy c d =
    canMatch c groundD
    where
        groundD = groundClause d


-- Returns true if there exists a substituition between c and d 
-- Such that applying the substitution to c produces a clause with a subset of the literals in d
-- Assumes d is a ground clause 
-- TODO: we perhaps want to think about the order in which the literals in c are considered 
-- to match literals in d 
-- We should choose the rarest literals in C first to match literals in d, since if there is no 
-- suitable match we will find out straight away 
canMatch :: Clause -> Clause -> Bool
canMatch (Clause cLiterals) (Clause dLiterals) = matchRemaining cLiterals Map.empty
  where
    -- Base Case: All literals in c have been successfully matched
    matchRemaining [] _ = True

    -- Recursive Step: match the first literal c against any literal 'd' in D
    matchRemaining (c:cs) currentSubst =
        let
            -- Find all literals in D that c can match given our current variable bindings
            validSubs = [ newSubst | d <- dLiterals, Just newSubst <- [matchLiterals c d currentSubst] ]
        in
            -- If any of these assignments allow the REST of the literals to match
            -- Then it is the case that there is a substitution that will make c a subset of d
            any (matchRemaining cs) validSubs


matchLiterals :: Literal -> Literal -> Sub -> Maybe Sub
matchLiterals (Pos p) (Pos q) sub = matchPredicates p q sub
matchLiterals (Neg p) (Neg q) sub = matchPredicates p q sub
matchLiterals _ _ _ = Nothing


matchPredicates :: Predicate -> Predicate -> Sub -> Maybe Sub
matchPredicates (R(p, pTerms)) (R(q, qTerms)) sub
    | p /= q = Nothing
    | length pTerms /= length qTerms = Nothing
    | otherwise = matchTerms pTerms qTerms sub


matchTerms :: [Term] -> [Term] -> Sub -> Maybe Sub
matchTerms [] [] sub = Just sub
matchTerms (x:xs) (y:ys) sub =
 if length xs /= length ys then Nothing
 else
    let
        maybeNewSub = matchTerm x y sub
    in
        case maybeNewSub of
            Nothing -> Nothing
            Just newSub -> matchTerms xs ys newSub
matchTerms _ _ _ = Nothing


matchTerm :: Term -> Term -> Sub -> Maybe Sub
matchTerm (Var x) t2 sub =
    case Map.lookup (Var x) sub of
        -- Var x is already bound
        -- If it is already bound to the term from the right hand side 
        -- then we dont need to do anything 
        -- otherwise we cannot find a valid substitution
        Just existingTerm ->
            if existingTerm == t2 then Just sub else Nothing

        -- Var x is new, and so we should bind it to the ground term from the right side
        Nothing -> Just (Map.insert (Var x) t2 sub)

matchTerm (Fn (f1, args1)) (Fn (f2, args2)) sub
    -- Functions must have the same name and arity.
    | f1 == f2 && length args1 == length args2 = matchTerms args1 args2 sub
    | otherwise = Nothing

-- a function on the left can never match a variable on the right.
-- since the right side is grounded, there shouldn't be any variables there anyway
matchTerm (Fn (_, _)) (Var _) _ = Nothing


