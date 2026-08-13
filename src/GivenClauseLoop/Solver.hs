{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module GivenClauseLoop.Solver (solve) where

import Control.Lens ( use, (%=), (+=), (.=) )
import Control.Monad.State ( MonadState(get), gets )

import GivenClauseLoop.State
    ( ProofSearch,
      ProofSearchState,
      activeSet,
      clauseTrie,
      isUnsat,
      stepsTaken,
      symbolOrdering,
      startTime, terminatingFunction )

import GivenClauseLoop.InferenceGeneration ( performInferences )
import GivenClauseLoop.PassiveQueueHandling
    ( switchPassiveQueue, selectClauseFromPassiveQueue )
import Subsumption.SubsumptionFilter
    ( getFeatureVector, insertInClauseTrie )
import GivenClauseLoop.Types ( DerivedClause(derived) )
import GivenClauseLoop.Timing (updateTimeElapsed)


-- Primary Given Clause Loop
solve :: ProofSearchState ProofSearch
solve = do
    unsat <- use isUnsat
    terminateFunction <- use terminatingFunction
    terminateSearch <- case terminateFunction of
        Just f -> gets f
        Nothing -> return False

    case (unsat, terminateSearch) of
        -- The formula is either satisfiable or unsatisfiable
        (Just _, _) -> get
        (_, True) -> get
        _ -> do
            maybeGivenClause <- selectClauseFromPassiveQueue

            case maybeGivenClause of
                -- The passive queue is empty, and we have saturated the search 
                -- Our formula is Satisfiable  
                Nothing -> do
                    isUnsat .= Just False
                    get

                -- Perfrom inferences with the selected clause 
                -- And update the prioirty queues 
                -- Progress the proof search 
                Just givenClause -> do
                    performInferences givenClause
                    activeSet %= (givenClause : )
                    ordering <- use symbolOrdering
                    clauseTrie %= insertInClauseTrie ordering givenClause.derived (getFeatureVector givenClause.derived)
                    switchPassiveQueue
                    stepsTaken += 1
                    startTime <- use startTime
                    updateTimeElapsed startTime
                    solve
