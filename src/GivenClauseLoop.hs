{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# HLINT ignore "Use null" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedRecordDot #-}
module GivenClauseLoop where
import Data.Aeson (ToJSON)
import FOL ( Clause (Clause), getLiterals, Literal)
import Unification (standardiseApartClause)
import Resolution (resolve)
import Factoring (factorise)
import Data.List (sortOn)
import GHC.Generics (Generic)
import Control.Monad.State
import Prelude hiding (id)
import qualified Data.Maybe

type ProofSearchState = State Int

-- A helper function to get a unique clause Id
getNextId :: ProofSearchState Int
getNextId = do
    current <- get
    put (current + 1)
    return current


data Step = Resolution | Factorisation deriving (Show, Generic, ToJSON)

data ProofSearch = Search { isUnsat :: Maybe Bool, actives :: [DerivedClause], passives:: [DerivedClause]} deriving (Show, Generic, ToJSON)

data DerivedClause =
    Derived {
        derived :: Clause,
        parent1 :: DerivedClause,
        parent2 :: DerivedClause,
        step :: Step,
        clauseId :: Int
        }
    | Axiom {derived :: Clause, clauseId:: Int}
    deriving (Show, Generic, ToJSON)



-- Given a list of list of literals as clauses 
-- Returns a list of axioms to be used as input to the solver
createAxioms :: [[Literal]] -> [DerivedClause]
createAxioms litsList =
    zipWith (\ lits i -> Axiom {derived = Clause lits, clauseId = i}) litsList [1..]
-- createAxioms :: [[Literal]] -> ProofSearchState [DerivedClause]
-- createAxioms = mapM createSingleAxiom
--   where
--     createSingleAxiom lits = do
--         newId <- getNextId
--         return (Axiom {axiom = Clause lits, id = newId})

-- Solves whether a set of clauses is unsatisfiable 
-- If the set is Unsatisfiable then True is returned 
-- If the set if Satisfiable then False is returned 
solve :: [Clause] -> Bool
solve initialClauses = givenClauseLoop initialClauses []

-- Takes a passive set and an active set and iterates through the 
-- passive set, at each step it derives all possible inferences 
-- between the passive clause and the active set. These derived clauses are then 
-- added to the passive set. If the passive set is empty, then we say that we have saturated the 
-- proof search, and the set of clauses is satisfiable 
-- If we derive the empty clause then the set of clauses is unsatisfiable   
givenClauseLoop :: [Clause] -> [Clause] -> Bool
givenClauseLoop [] _ = False
givenClauseLoop (Clause x:xs) actives =
    x == [] || givenClauseLoop sortedPassives newActives
            where
                resolved = concatMap (resolution (Clause x)) actives
                factored = map Clause (factorise x)
                newPassives = xs ++ resolved ++ factored
                sortedPassives = sortOn (length . getLiterals) newPassives
                newActives = Clause x : actives

-- Runs a proof search for N Steps 
-- Returns the passive and active sets created 
-- And Maybe a result
proofSearchAfterNSteps :: Int -> [DerivedClause] -> [DerivedClause] -> ProofSearchState ProofSearch
proofSearchAfterNSteps _ [] actives = return Search {isUnsat= Just False, actives = actives, passives = []}
proofSearchAfterNSteps 0 passives actives = return Search{isUnsat = Nothing, actives = actives, passives = passives}
proofSearchAfterNSteps n (selected: passives) actives =
    do
        factored <- factorisingWithDerivedClause selected
        resolved <- concat <$> mapM (resolutionWithDerivedClauses selected) actives
        let newPassives = passives ++ factored ++ resolved
        let newActives = selected : actives
        let sortedPassives = sortOn (length . getLiterals . derived) newPassives
        let unsat = derivedFalse sortedPassives
        if unsat then return Search {isUnsat = Just True, actives = selected : newActives, passives = newPassives}
        else proofSearchAfterNSteps (n-1) sortedPassives newActives

-- Solves a problem and returns the passive and active sets created during the proof search as well as the result 
solveWithProofSearch :: [DerivedClause] -> [DerivedClause] -> ProofSearchState ProofSearch

solveWithProofSearch [] actives = return Search {isUnsat = Just False, actives = actives, passives = []}

solveWithProofSearch (current@(Derived {derived = Clause []}) : passives) actives =
    return Search { isUnsat = Just True, actives = current : actives, passives = passives }

solveWithProofSearch (selected : passives) actives =
            do
                factored <- factorisingWithDerivedClause selected
                resolved <- concat <$> mapM (resolutionWithDerivedClauses selected) actives
                let newPassives = passives ++ factored ++ resolved
                let newActives = selected : actives
                let sortedPassives = sortOn (length . getLiterals . derived) newPassives
                let unsat = derivedFalse sortedPassives
                if unsat then return Search {isUnsat = Just True, actives = selected : newActives, passives = newPassives}
                else solveWithProofSearch sortedPassives newActives


-- Solves a problem, and if Unsatisfiable returns a DerivedClause Object from which the proof can be obtained 
solveWithProof :: [DerivedClause] -> [DerivedClause] -> ProofSearchState (Maybe DerivedClause)
solveWithProof [] _ = return Nothing
solveWithProof (selected@(Derived {derived = Clause []}): _) _ = return (Just selected)
solveWithProof (selected: passives) actives =
    do
        factored <- factorisingWithDerivedClause selected
        resolved <- concat <$> mapM (resolutionWithDerivedClauses selected) actives
        let newPassives = passives ++ factored ++ resolved
        let newActives = selected : actives
        let sortedPassives = sortOn (length . getLiterals . derived) newPassives
        let unsat = derivedFalseClause sortedPassives
        if Data.Maybe.isJust unsat then return unsat
        else solveWithProof sortedPassives newActives


-- Returns True if the empty clause is contained in the list 
derivedFalse :: [DerivedClause] -> Bool
derivedFalse = foldr (\ x -> (||) (x.derived == Clause [])) False

derivedFalseClause :: [DerivedClause] -> Maybe DerivedClause
derivedFalseClause [] = Nothing
derivedFalseClause (x:xs) = if x.derived == Clause [] then Just x
                            else derivedFalseClause xs


-- Performs resolution with derived clause type 
-- Labels each clause with a unique id
resolutionWithDerivedClauses :: DerivedClause -> DerivedClause -> ProofSearchState [DerivedClause]
resolutionWithDerivedClauses active selected = do
    let activeLits = getLiterals active.derived
    let selectedLits = getLiterals selected.derived
    let stdSelected = standardiseApartClause activeLits selectedLits
    let results = resolve stdSelected activeLits
    mapM (createDerived . Clause)  results
    where
        createDerived clauseBody = do
            newId <- getNextId
            return Derived
                {
                    derived = clauseBody,
                    parent1 = active,
                    parent2 = selected,
                    clauseId = newId,
                    step = Resolution
                }

-- Given two clauses  
-- Standardise apart the two clauses 
-- And return all the possible clauses created using resolution
-- Returns all the possible clauses you can derive between them  
resolution :: Clause -> Clause -> [Clause]
resolution (Clause active_clause) (Clause selected_clause) =
    map Clause (resolve standardised_selected_clause active_clause)
    where
    standardised_selected_clause = standardiseApartClause active_clause selected_clause

-- Performs factorisation with DerivedClause Type 
-- Labels each new clause with a type 
factorisingWithDerivedClause :: DerivedClause -> ProofSearchState [DerivedClause]
factorisingWithDerivedClause clause = do
    let clauseLiterals = getLiterals clause.derived
    let factorisedClauses = factorise clauseLiterals
    mapM (createDerived . Clause) factorisedClauses
    where
        createDerived clauseBody = do
            newId <- getNextId
            return Derived
                {
                    derived = clauseBody,
                    parent1 = clause,
                    parent2 = clause,
                    clauseId = newId,
                    step = Factorisation
                }
