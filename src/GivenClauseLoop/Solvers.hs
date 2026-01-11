-- Contains functions to solve a problem 
-- And return a boolean indicating satisfiability 

module GivenClauseLoop.Solvers where

import Data.List ( foldl', sortOn )
import qualified Data.PQueue.Prio.Min as PQ

import FOL (Clause (..), getLiterals)
import GivenClauseLoop.Types (PassiveSetPriorityQueue)
import Factoring (factorise)
import Utils (isTautology)
import GivenClauseLoop.Helpers (resolution)

-- Solves whether a set of clauses is unsatisfiable 
-- If the set is Unsatisfiable then True is returned 
-- If the set if Satisfiable then False is returned 
solve :: [Clause] -> Bool
solve initialClauses = givenClauseLoop initialClauses []

solvePQ :: [Clause] -> Bool
solvePQ initialClauses = givenClauseLoopPQ (PQ.fromList (map getPriority initialClauses)) []

getPriority :: Clause -> (Int, Clause)
getPriority clause = (length $ getLiterals  clause, clause)


-- Takes a passive set and an active set and iterates through the 
-- passive set, at each step it derives all possible inferences 
-- between the passive clause and the active set. These derived clauses are then 
-- added to the passive set. If the passive set is empty, then we say that we have saturated the 
-- proof search, and the set of clauses is satisfiable 
-- If we derive the empty clause then the set of clauses is unsatisfiable   
givenClauseLoop :: [Clause] -> [Clause] -> Bool
givenClauseLoop [] _ = False
givenClauseLoop (Clause []:_) _ = True
givenClauseLoop (Clause x:xs) actives =
    unsat || givenClauseLoop sortedPassives newActives
        where
            resolved = concatMap (resolution (Clause x)) actives
            factored = map Clause (factorise x)
            derivedClauses = filter (not . isTautology) (factored ++ resolved)
            newPassives = xs ++ derivedClauses
            sortedPassives = sortOn (length . getLiterals) newPassives
            newActives = Clause x : actives
            unsat = Clause [] `elem` derivedClauses


-- This implementation of the given clause loop 
-- Uses a prioirty queue to handle the passive set 
-- Orders the priority queue by weight 
givenClauseLoopPQ :: PassiveSetPriorityQueue -> [Clause] -> Bool
givenClauseLoopPQ passives actives = case PQ.minView passives of
    Nothing -> False
    Just (Clause [], _) -> True
    Just (currentClause, restPassives) ->
        unsat || givenClauseLoopPQ updatedPassives newActives
        where
            resolved = concatMap (resolution currentClause) actives
            factored = map Clause (factorise (getLiterals currentClause))
            derivedClauses  = filter (not . isTautology) (factored ++ resolved)
            updatedPassives = foldl' (\pq c -> PQ.insert (length (getLiterals c)) c pq) restPassives derivedClauses
            newActives = currentClause : actives
            unsat = Clause [] `elem` derivedClauses