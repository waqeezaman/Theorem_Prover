{-# LANGUAGE OverloadedRecordDot #-}

module Scheduler (runSchedule) where

import Control.Concurrent.Async (async, cancel, wait)
import Control.Concurrent.STM (newTVarIO, atomically, readTVar, writeTVar)
import Control.Concurrent.MVar (newEmptyMVar, tryPutMVar, takeMVar)
import System.Timeout (timeout)
import Data.Time.Clock.System (getSystemTime)
import Control.Monad (replicateM, void)

import GivenClauseLoop.State ( ProofSearch(_isUnsat), initialiseState )
import FOL ( Clause )
import GivenClauseLoop.Solver (solve)
import PassiveQueue (pqConfigToPQ)
import Filtering (composeFilteringTypesIntoFilterFunction)
import GivenClauseLoop.Termination (terminateTimeOutOrStepLimit)
import Control.Monad.State (evalStateT)
import Data.Maybe (isJust)
import Config
    ( Schedule(Schedule),
      SingleProofSearchOptions(stopAfterNSteps, passiveQueues,
                               filterFunction, timeLimit),
      ProofSearchConfig(threads, schedule, totalTimeLimit) )


-- Executes the schedule across N threads with a global timeout.
runSchedule :: ProofSearchConfig -> [Clause] -> IO (Maybe ProofSearch)
runSchedule config clauses = do
    let strategies = config.schedule

    -- Create a thread-safe queue of the strategies we need to try
    jobQueue <- newTVarIO strategies

    -- The first thread to succeed puts its result in this MVar
    successVar <- newEmptyMVar

    -- Define the worker loop for a single thread
    let worker = do
          -- Pop the next strategy from the queue
          nextJob <- atomically $ do
              jobs <- readTVar jobQueue
              case jobs of
                  (Schedule []) -> return Nothing
                  (Schedule (j:js)) -> do
                      writeTVar jobQueue (Schedule js)
                      return (Just j)

          case nextJob of
              Nothing -> return () -- No jobs left, thread retires gracefully
              Just opt -> do
                  -- Evaluate state monad into IO here. 
                  finalState <- executeSearch opt clauses

                  -- Check if this specific search yielded a proof
                  if isProofFound finalState
                      then void $ tryPutMVar successVar (Just finalState)
                      else worker -- Failed to find a proof, loop back and grab the next job

    -- Convert the total time limit to microseconds for System.Timeout
    -- If Nothing, we use -1
    let timeLimitMicros = maybe (-1) (* 1000000) config.totalTimeLimit

    -- The orchestration logic
    let runWorkers = do
          -- Spawn N worker threads
          workerAsyncs <- replicateM config.threads (async worker)

          -- We also need a way to know if ALL workers fail and the queue empties
          -- We spawn a watcher thread that waits for all workers to finish
          -- If they all finish naturally, we put 'Nothing' in the successVar
          allDoneAsync <- async $ do
              mapM_ wait workerAsyncs
              void $ tryPutMVar successVar Nothing

          -- Block until a result (Just or Nothing) is put into the MVar
          result <- takeMVar successVar

          -- Cleanup: Cancel all running threads
          mapM_ cancel workerAsyncs
          cancel allDoneAsync

          return result

    -- Execute with or without the global timeout
    if timeLimitMicros > 0
       then do
           timedOutResult <- timeout timeLimitMicros runWorkers
           case timedOutResult of
               Nothing -> return Nothing -- The global timeout was reached
               Just res -> return res    -- The search finished (success or exhausted) before timeout
       else runWorkers



executeSearch :: SingleProofSearchOptions -> [Clause] -> IO ProofSearch
executeSearch options clauses = do
    -- Initialise state with options
    let pq = map pqConfigToPQ options.passiveQueues
    let filteringFunction = composeFilteringTypesIntoFilterFunction options.filterFunction
    let terminalFunction = terminateTimeOutOrStepLimit options.timeLimit options.stopAfterNSteps
    currentTime <- getSystemTime
    let initialState = initialiseState clauses pq filteringFunction currentTime (Just terminalFunction)
    -- Evaluate and return the final state of the search
    evalStateT solve initialState


-- Checks the final state of a search to see if a proof was successfully found
isProofFound :: ProofSearch -> Bool
isProofFound finalState = isJust finalState._isUnsat
