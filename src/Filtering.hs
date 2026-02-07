{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Filtering (
    filteringTypeToFilterFunction,
    composeFilteringTypesIntoFilterFunction,
    FilteringType(..)
    ) where

import Control.Monad.Extra (allM)
import GivenClauseLoop.Types (DerivedClause (..))
import Utils (isTautology)
import Control.Lens (use)
import Subsumption.Subsumption (isSubsumedBySeenClauses)
import Data.Aeson (FromJSON)
import GHC.Generics (Generic)
import GivenClauseLoop.State
    ( ProofSearchState, clauseTrie, symbolOrdering )


data FilteringType = NoFilter | RemoveTautologies | ForwardSubsumption deriving (Generic, FromJSON)

-- Takes a list of filtering types 
-- Returns the function that is the conjunction of all the individual filterinf functions 
-- e.g Filter1 AND Filter2 AND Filter3 ... 
-- This means a clause is only kept if all the filters think it should be kept 
composeFilteringTypesIntoFilterFunction :: [FilteringType] ->  (DerivedClause -> ProofSearchState Bool)
composeFilteringTypesIntoFilterFunction filteringTypes =
        \clause -> allM ($ clause) filteringFunctions
    where
        filteringFunctions = map filteringTypeToFilterFunction filteringTypes


filteringTypeToFilterFunction :: FilteringType ->  (DerivedClause -> ProofSearchState Bool)
filteringTypeToFilterFunction  filterType = case filterType of
    NoFilter -> noFilter
    RemoveTautologies -> tautologyFilter
    ForwardSubsumption -> subsumptionFilter


-- Applies no filtering
noFilter :: DerivedClause -> ProofSearchState Bool
noFilter _ = return True

-- Only keeps a clause if it is not a tautology 
tautologyFilter :: DerivedClause -> ProofSearchState Bool
tautologyFilter clause = return (not $ isTautology clause.derived)

-- Only keep a clause if it is not subsumed by previosly seen clauses 
subsumptionFilter :: DerivedClause -> ProofSearchState Bool
subsumptionFilter clause = do
        trie <- use clauseTrie
        ordering <- use symbolOrdering
        return (not $ isSubsumedBySeenClauses clause.derived ordering trie)

