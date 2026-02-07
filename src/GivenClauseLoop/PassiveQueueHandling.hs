{-# LANGUAGE OverloadedRecordDot #-}

module GivenClauseLoop.PassiveQueueHandling (
    switchPassiveQueue,
    addClausesToPassiveQueues,
    selectClauseFromPassiveQueue) where 

import GivenClauseLoop.State
    ( ProofSearchState,
      currentPassiveQueueCounter,
      currentPassiveQueueIndex,
      passiveQueues,
      processedClauses ) 
import GivenClauseLoop.Types ( DerivedClause(clauseId) ) 
import Control.Lens ( (^.), use, (%=), (+=), (.=), Ixed(ix) )
import PassiveQueue ( queue, weight, addToPassiveQueue )
import Control.Monad ( when )
import qualified Data.PQueue.Prio.Min as PQ
import qualified Data.Set as Set

-- Checks if we need to switch to a different passive queue 
-- Increments passive queue counters 
-- Resets the counter if we need to swicth queues 
switchPassiveQueue :: ProofSearchState ()
switchPassiveQueue = do
    currentIndex <- use currentPassiveQueueIndex
    queues <- use passiveQueues
    let selectedQueue = queues !! currentIndex
    currentPassiveQueueCounter += 1
    counter <- use currentPassiveQueueCounter
    when (counter >= selectedQueue ^. weight) $ do
        currentPassiveQueueIndex .= (currentIndex+1) `mod` length queues
        currentPassiveQueueCounter .= 0

addClausesToPassiveQueues :: [DerivedClause] -> ProofSearchState ()
addClausesToPassiveQueues newClauses =
    -- For each queue in the passive queue 
    -- Add each new clause to the passive queue
    passiveQueues %= \queues ->
        map (\pq -> foldl addToPassiveQueue pq newClauses) queues

-- Removes a clause from a single passive queue 
-- Check if the clause has laready been processed 
-- If the clause has already been processed 
-- Selects another clause from the passive queue 
-- Updates processed clauses 
selectClauseFromPassiveQueue :: ProofSearchState (Maybe DerivedClause)
selectClauseFromPassiveQueue = do

    seenClauses <- use processedClauses
    currentQueueIndex <- use currentPassiveQueueIndex
    queues <- use passiveQueues

    let currentQueue = queues !! currentQueueIndex
    case PQ.minView (currentQueue ^. queue) of
        Nothing ->
            return Nothing
        Just (clause, remainingPQ) -> do
            -- Update current queue
            passiveQueues . ix currentQueueIndex . queue .= remainingPQ
            -- Ignore this cluase if we have already seen this clause 
            -- (i.e. the clause has been popped by a previous pq)
            if clause.clauseId `elem` seenClauses then
                selectClauseFromPassiveQueue
            -- Otherwise this is the selected clause
            -- And add the clause to the set of processed clauses 
            else
                do
                processedClauses %= Set.insert clause.clauseId
                return (Just clause)
