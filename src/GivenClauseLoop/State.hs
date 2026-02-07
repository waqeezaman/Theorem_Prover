{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module GivenClauseLoop.State where

import GivenClauseLoop.Helpers ( createAxioms)
import Control.Lens ( makeLenses )
import Control.Monad.State ( State )
import qualified Data.Set as Set

import FOL (Clause (..))
import GivenClauseLoop.Types (DerivedClause (..) )
import Subsumption.SubsumptionFilter (ClauseTrie, emptyClauseTrie, getSymbolOrder)
import PassiveQueue(PassiveQueue, addToPassiveQueue)


type ProofSearchState = State ProofSearch

data ProofSearch = ProofSearch
    {
        _axioms :: [DerivedClause],
        _activeSet :: [DerivedClause],
        _passiveQueues :: [PassiveQueue],
        _currentPassiveQueueIndex :: Int,
        _currentPassiveQueueCounter :: Int,
        _processedClauses :: Set.Set Int,
        _filterFunction :: DerivedClause -> ProofSearchState Bool,
        _clauseTrie :: ClauseTrie,
        _isUnsat :: Maybe Bool,
        _stepsTaken :: Int,
        _stopAfterNSteps :: Maybe Int,
        _currentClauseId :: Int,
        _symbolOrdering :: [String],
        _derivation :: Maybe DerivedClause
    }

makeLenses ''ProofSearch

initialiseState :: [Clause] -> Maybe Int ->  [PassiveQueue] -> (DerivedClause -> ProofSearchState Bool) -> ProofSearch
initialiseState axioms stopAfterNSteps passiveQueues filterFunction = 
    ProofSearch
    {
        _axioms = derivedAxioms,
        _activeSet = [],
        _passiveQueues = initialisedPassiveQueues,
        _currentPassiveQueueIndex = 0,
        _currentPassiveQueueCounter = 0,
        _processedClauses = Set.empty,
        _filterFunction = filterFunction,
        _clauseTrie = emptyClauseTrie,
        _isUnsat = Nothing,
        _stepsTaken = 0,
        _stopAfterNSteps = stopAfterNSteps,
        _currentClauseId = currentClauseId,
        _symbolOrdering = getSymbolOrder axioms,
        _derivation = Nothing
    }
    where 
        derivedAxioms = createAxioms axioms
        currentClauseId = length derivedAxioms + 1
        -- Insert all axioms into passive queues
        initialisedPassiveQueues = map (\pq -> foldl addToPassiveQueue pq derivedAxioms) passiveQueues

