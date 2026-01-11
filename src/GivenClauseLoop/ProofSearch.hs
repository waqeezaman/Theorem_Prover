-- Conatins functions to solve a problem 
-- And return either the proof or the proof search 

module GivenClauseLoop.ProofSearch where

import GivenClauseLoop.Types (DerivedClause (..), ProofSearch (..), ProofSearchState)
import FOL (Clause(..), getLiterals)
import GivenClauseLoop.Helpers
    ( derivedFalse,
      derivedFalseClause,
      resolutionWithDerivedClauses,
      factorisingWithDerivedClause )
import Utils (isTautology)
import Data.List (sortOn)
import Data.Maybe (isJust)

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
        let derivedClauses = filter (not . isTautology . derived) (factored ++ resolved)
        let newPassives = passives ++ derivedClauses
        let sortedPassives = sortOn (length . getLiterals . derived) newPassives
        let newActives = selected : actives
        let unsat = derivedFalse derivedClauses
        if unsat then return Search {isUnsat = Just True, actives = selected : newActives, passives = sortedPassives}
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
                let derivedClauses = filter (not . isTautology . derived) (factored ++ resolved)
                let newPassives = passives ++ derivedClauses
                let sortedPassives = sortOn (length . getLiterals . derived) newPassives
                let newActives = selected : actives
                let unsat = derivedFalse derivedClauses
                if unsat then return Search {isUnsat = Just True, actives = selected : newActives, passives = sortedPassives}
                else solveWithProofSearch sortedPassives newActives


-- Solves a problem, and if Unsatisfiable returns a DerivedClause Object from which the proof can be obtained 
solveWithProof :: [DerivedClause] -> [DerivedClause] -> ProofSearchState (Maybe DerivedClause)
solveWithProof [] _ = return Nothing
solveWithProof (selected@(Derived {derived = Clause []}): _) _ = return (Just selected)
solveWithProof (selected: passives) actives =
    do
        factored <- factorisingWithDerivedClause selected
        resolved <- concat <$> mapM (resolutionWithDerivedClauses selected) actives
        let derivedClauses = filter (not . isTautology . derived) (factored ++ resolved)
        let newPassives = passives ++ derivedClauses
        let sortedPassives = sortOn (length . getLiterals . derived) newPassives
        let newActives = selected : actives
        let unsat = derivedFalseClause derivedClauses
        if isJust unsat then return unsat
        else solveWithProof sortedPassives newActives
