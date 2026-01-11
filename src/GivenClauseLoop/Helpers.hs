{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# HLINT ignore "Use null" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE OverloadedRecordDot #-}

module GivenClauseLoop.Helpers where

import GivenClauseLoop.Types
    ( DerivedClause(..),
      Step(Factorisation, Resolution),
      ProofSearchState )
import FOL (Clause (..), getLiterals, Literal)
import Unification (standardiseApartClause)
import Resolution (resolve)
import Factoring (factorise)


import Control.Monad.State ( MonadState(put, get) )
import Prelude hiding (id)

createAxioms :: [[Literal]] -> [DerivedClause]
createAxioms litsList =
    zipWith (\ lits i -> Axiom {derived = Clause lits, clauseId = i}) litsList [1..]

-- A helper function to get a unique clause Id
getNextId :: ProofSearchState Int
getNextId = do
    current <- get
    put (current + 1)
    return current

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
