{-# LANGUAGE OverloadedRecordDot #-}

module GivenClauseLoop.InferenceGeneration (performInferences) where 
    
import FOL ( Clause(..), getLiterals )
import GivenClauseLoop.Types( DerivedClause(Derived, derived, step, parent1, parent2,clauseId),Step(..))
import GivenClauseLoop.State
    ( ProofSearchState,
      activeSet,
      currentClauseId,
      derivation,
      filterFunction,
      isUnsat )
import Control.Lens ( use, (<<+=), (.=) )
import Unification ( standardiseApartClause )
import Resolution ( resolve )
import Factoring ( factorise )
import Control.Monad ( filterM )
import GivenClauseLoop.Helpers ( derivedFalseClause )
import Data.Maybe ( isJust )
import GivenClauseLoop.PassiveQueueHandling
    ( addClausesToPassiveQueues )


incrementId :: ProofSearchState Int
incrementId = currentClauseId <<+= 1

-- Given a selected clause finds all clauses generated using resolution 
-- between the selected clause and the passive set 
-- generates new clauses with proper clause Ids
statefulResolution :: DerivedClause -> ProofSearchState [DerivedClause]
statefulResolution selected =
    do
        actives <- use activeSet
        results <- mapM (statefulResolution' selected) actives
        return (concat results)


-- Performs resolution between two clauses 
-- Generates clauses with proper clause Ids
statefulResolution' :: DerivedClause -> DerivedClause -> ProofSearchState [DerivedClause]
statefulResolution' selected active =
    do
        let activeLits = getLiterals active.derived
        let selectedLits = getLiterals selected.derived
        let stdSelected = standardiseApartClause activeLits selectedLits
        let results = resolve stdSelected activeLits
        mapM (\c -> createDerivedClause Resolution (Clause c) selected active)  results


-- Factorises a clause 
-- and generare new clauses with proper clause Ids
statefulFactorisation :: DerivedClause -> ProofSearchState [DerivedClause]
statefulFactorisation selected = do
    let clauseLiterals = getLiterals selected.derived
    let factorisedClauses = factorise clauseLiterals
    mapM (\c -> createDerivedClause Factorisation (Clause c) selected selected) factorisedClauses

-- Creates a new derived clause with a unique clause Id 
-- Increments clause id counter 
createDerivedClause :: Step -> Clause -> DerivedClause -> DerivedClause -> ProofSearchState DerivedClause
createDerivedClause step newClause parent1 parent2 = do
    nextId <- incrementId
    return Derived {
        step = step,
        derived = newClause,
        parent1 = parent1,
        parent2 = parent2,
        clauseId = nextId
    }

-- Generate clause using resolution 
-- Generate clauses using factorisation
-- Filter clauses using defined Filter function  
-- Checks if we have derived empty clause  
-- Adds clauses to passive queues 
performInferences :: DerivedClause -> ProofSearchState ()
performInferences selectedClause =
    do
        resolvedClauses <- statefulResolution selectedClause
        factorisedClauses <- statefulFactorisation selectedClause
        filterFn <- use filterFunction
        filteredClauses <- filterM filterFn (resolvedClauses ++ factorisedClauses)
        let falseClause = derivedFalseClause filteredClauses 
        isUnsat .= if isJust falseClause then Just True else Nothing  
        derivation .= falseClause
        addClausesToPassiveQueues filteredClauses

