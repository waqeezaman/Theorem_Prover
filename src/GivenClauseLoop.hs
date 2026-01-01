module GivenClauseLoop where
import FOL ( Literal )
import Unification (standardiseApartClause)
import Resolution (resolve)
import Factoring (factorise)

-- Solves whether a set of clauses is unsatisfiable 
-- If the set is Unsatisfiable then False is returned 
-- If the set if Satisfiable then True is returned 
solve :: [[Literal]] -> Bool
solve initialClauses = givenClauseLoop initialClauses []

-- Takes a passive set and an active set and iterates through the 
-- passive set, at each step it derives all possible inferences 
-- between the passive clause and the active set. These derived clauses are then 
-- added to the passive set. If the passive set is empty, then we say that we have saturated the 
-- proof search, and the set of clauses is satisfiable 
-- If we derive the empty clause then the set of clauses is unsatisfiable   
givenClauseLoop :: [[Literal]] -> [[Literal]] -> Bool
givenClauseLoop [] _ = True
givenClauseLoop (x:xs) actives =
    (x /= []) && givenClauseLoop newPassives newActives
            where
                derived = concatMap (derive x) actives
                newPassives = xs ++ derived
                newActives = x : actives

-- Given an initial set of passive and active clauses 
-- Returns all the clauses derivied during a proof search 
findAllDerivedClauses :: [[Literal]] -> [[Literal]] -> [[Literal]]
findAllDerivedClauses [] actives = actives 
findAllDerivedClauses (x:xs) actives =
    findAllDerivedClauses newPassives newActives
            where
                derived = concatMap (derive x) actives
                newPassives = xs ++ derived
                newActives = x : actives


-- derives all possible inferences between two clauses
derive :: [Literal] -> [Literal] -> [[Literal]]
derive clause1 clause2 = 
    resolvedClauses ++ factoredClauses
    where 
        resolvedClauses = resolution clause1 clause2
        factoredClauses = factorising resolvedClauses

-- Given two clauses  
-- Standardise aprt the two clauses 
-- And return all the possible clauses created using resolution
-- Returns all the possible clauses you can derive between them  
resolution :: [Literal] -> [Literal] -> [[Literal]]
resolution active_clause selected_clause =
    resolve standardised_selected_clause active_clause
    where
    standardised_selected_clause = standardiseApartClause active_clause selected_clause

factorising :: [[Literal]] -> [[Literal]]
factorising = concatMap factorise