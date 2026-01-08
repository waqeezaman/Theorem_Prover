{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# HLINT ignore "Use null" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module GivenClauseLoop where
import Data.Aeson (ToJSON)
import FOL ( Literal, Clause (Clause), getLiterals)
import Unification (standardiseApartClause)
import Resolution (resolve)
import Factoring (factorise)
import Data.List (sortOn)
import GHC.Generics (Generic)

data DerivedClause = Derived {derived::Clause, parent1 :: Clause, parent2 :: Clause} deriving (Show, Generic, ToJSON)
data ProofResult = Result { isUnsat :: Bool, actives :: [DerivedClause], passives:: [DerivedClause]} deriving (Show, Generic, ToJSON)

-- Solves whether a set of clauses is unsatisfiable 
-- If the set is Unsatisfiable then True is returned 
-- If the set if Satisfiable then False is returned 
solve :: [[Literal]] -> Bool
solve initialClauses = givenClauseLoop initialClauses []

-- Takes a passive set and an active set and iterates through the 
-- passive set, at each step it derives all possible inferences 
-- between the passive clause and the active set. These derived clauses are then 
-- added to the passive set. If the passive set is empty, then we say that we have saturated the 
-- proof search, and the set of clauses is satisfiable 
-- If we derive the empty clause then the set of clauses is unsatisfiable   
givenClauseLoop :: [[Literal]] -> [[Literal]] -> Bool
givenClauseLoop [] _ = False
givenClauseLoop (x:xs) actives =
    x == [] || givenClauseLoop sortedPassives newActives
            where
                resolved = concatMap (resolution x) actives
                factored = factorise x
                newPassives = xs ++ resolved ++ factored
                sortedPassives = sortOn length newPassives
                newActives = x : actives

-- Given an initial set of passive and active clauses 
-- Returns all the clauses derivied during a proof search 
findAllDerivedClauses :: [[Literal]] -> [[Literal]] -> [[Literal]]
findAllDerivedClauses [] actives = actives
findAllDerivedClauses (x:xs) actives =
    findAllDerivedClauses sortedPassives newActives
            where
                resolved = concatMap (resolution x) actives
                factored = factorise x
                newPassives = xs ++ resolved ++ factored
                sortedPassives = sortOn length newPassives
                newActives = x : actives

-- Given an initial set of passive and active clauses 
-- Returns all the clauses derivied during a proof search 
findDerivedClausesForNSteps :: [[Literal]] -> [[Literal]] -> Integer -> [[Literal]]
findDerivedClausesForNSteps [] actives _ = actives
findDerivedClausesForNSteps passives actives 0 = actives ++ passives
findDerivedClausesForNSteps (x:xs) actives n =
    findDerivedClausesForNSteps sortedPassives newActives (n-1)
            where
                resolved = concatMap (resolution x) actives
                factored = factorise x
                newPassives = xs ++ resolved ++ factored
                sortedPassives = sortOn length newPassives
                newActives = x : actives

-- Performs a Proof Search for N steps 
-- Records each active clause in the proof search 
-- As well as the parents of the active clause 
proofSearchAfterNSteps :: [([Literal], [Literal], [Literal])] -> [([Literal], [Literal], [Literal])] -> Integer -> [([Literal],[Literal], [Literal])]
proofSearchAfterNSteps passives actives n = case (passives, actives, n) of
    ([], actives, _) -> actives
    (([], p1, p2):_, actives, _) -> actives ++ [([], p1, p2)]
    (_, _, 0) -> actives
    ((selected, parent1, parent2):xs, actives, n) ->
        proofSearchAfterNSteps sortedPassives newActives (n-1)
            where
                factored = factorisingWithParent selected
                resolved = concatMap (resolutionWithParents selected . (\(clause, _, _) -> clause)) actives
                newPassives = xs ++ resolved ++ factored
                sortedPassives = sortOn (\(x,_,_)-> length x) newPassives
                newActives = (selected, parent1, parent2) : actives


solveWithResult :: [DerivedClause] -> [DerivedClause] -> ProofResult
solveWithResult [] actives = Result {isUnsat = False, actives = actives, passives = []}
solveWithResult (current@(Derived (Clause []) _ _) : passives) actives = Result { isUnsat = True, actives = current : actives, passives = passives }
solveWithResult (selected : passives) actives =
        if unsat then Result {isUnsat = True, actives = selected : newActives, passives = newPassives}
        else solveWithResult newPassives newActives
    where
        unsat = derivedFalse sortedPassives
        newPassives = passives ++ factored ++ resolved
        sortedPassives = sortOn (length . getLiterals . derived) newPassives
        newActives = selected : actives
        factored = factorisingWithParent2 (derived selected)
        resolved = concatMap (resolutionWithParents2 (derived selected) . derived) actives

derivedFalse :: [DerivedClause] -> Bool 
derivedFalse [] = False 
derivedFalse (x:_) = case x of 
    (Derived (Clause []) _ _) -> True 
    _ -> False

-- Performs resolution between two clauses 
-- Returns all possible resolutions between the two clauses 
-- As well as returning the parents for each derived clause 
resolutionWithParents2 :: Clause -> Clause -> [DerivedClause]
resolutionWithParents2 clauseA clauseB =
    map (\x -> Derived{derived = x, parent1 = clauseA, parent2 = clauseB}) resolvedClauses
    where
         resolvedClauses = resolution2 clauseA clauseB


-- Given two clauses  
-- Standardise aprt the two clauses 
-- And return all the possible clauses created using resolution
-- Returns all the possible clauses you can derive between them  
resolution2 :: Clause -> Clause -> [Clause]
resolution2 (Clause active_clause) (Clause selected_clause) =
    map Clause (resolve standardised_selected_clause active_clause)
    where
    standardised_selected_clause = standardiseApartClause active_clause selected_clause



-- Performs resolution between two clauses 
-- Returns all possible resolutions between the two clauses 
-- As well as returning the parents for each derived clause 
resolutionWithParents :: [Literal] -> [Literal] -> [([Literal], [Literal], [Literal])]
resolutionWithParents clauseA clauseB =
    map (\x -> (x, clauseA, clauseB)) resolvedClauses
    where
         resolvedClauses = resolution clauseA clauseB


-- Given two clauses  
-- Standardise aprt the two clauses 
-- And return all the possible clauses created using resolution
-- Returns all the possible clauses you can derive between them  
resolution :: [Literal] -> [Literal] -> [[Literal]]
resolution active_clause selected_clause =
    resolve standardised_selected_clause active_clause
    where
    standardised_selected_clause = standardiseApartClause active_clause selected_clause


factorisingWithParent2 :: Clause -> [DerivedClause]
factorisingWithParent2 (Clause clause) = map (\fc -> Derived {derived = Clause fc, parent1 = Clause clause, parent2 = Clause clause}) factorisedClauses
    where factorisedClauses = factorise clause

factorisingWithParent :: [Literal] -> [([Literal], [Literal], [Literal])]
factorisingWithParent clause = map (\fc -> (fc, clause, clause)) factorisedClauses
    where factorisedClauses = factorise clause