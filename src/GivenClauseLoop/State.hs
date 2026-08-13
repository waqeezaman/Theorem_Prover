{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module GivenClauseLoop.State where

import GivenClauseLoop.Helpers ( createAxioms)
import Control.Lens ( makeLenses )
import Control.Monad.State ( StateT )
import qualified Data.Set as Set
import Data.Time.Clock.System ( SystemTime ) 

import FOL (Clause (..))
import GivenClauseLoop.Types (DerivedClause (..) )
import Subsumption.SubsumptionFilter (ClauseTrie, emptyClauseTrie, getSymbolOrder)
import PassiveQueue(PassiveQueue, addToPassiveQueue)


type ProofSearchState a = StateT ProofSearch IO a

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
        _currentClauseId :: Int,
        _symbolOrdering :: [String],
        _derivation :: Maybe DerivedClause,
        _startTime :: SystemTime,
        _timeElapsed :: Double, 
        _terminatingFunction :: Maybe (ProofSearch -> Bool)
    }

makeLenses ''ProofSearch

initialiseState :: [Clause] ->  [PassiveQueue] -> (DerivedClause -> ProofSearchState Bool) -> SystemTime -> Maybe (ProofSearch -> Bool)-> ProofSearch
initialiseState axioms passiveQueues filterFunction startTime terminatingFunction = 
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
        _currentClauseId = currentClauseId,
        _symbolOrdering = getSymbolOrder axioms,
        _derivation = Nothing,
        _startTime = startTime,
        _timeElapsed = 0.0,
        _terminatingFunction = terminatingFunction
    }
    where 
        derivedAxioms = createAxioms axioms
        currentClauseId = length derivedAxioms + 1
        -- Insert all axioms into passive queues
        initialisedPassiveQueues = map (\pq -> foldl addToPassiveQueue pq derivedAxioms) passiveQueues
