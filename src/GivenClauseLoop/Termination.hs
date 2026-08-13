module GivenClauseLoop.Termination where

import GivenClauseLoop.State (ProofSearch, _timeElapsed, _stepsTaken)

terminateTimeOut :: Double -> (ProofSearch -> Bool)
terminateTimeOut maxTime proofSearch = _timeElapsed proofSearch >= maxTime

terminateStepLimit :: Int -> (ProofSearch -> Bool)
terminateStepLimit maxSteps proofSearch = _stepsTaken proofSearch >= maxSteps

terminateTimeOutOrStepLimit :: Maybe Double -> Maybe Int -> (ProofSearch -> Bool)
terminateTimeOutOrStepLimit maybeMaxTime maybeMaxSteps proofSearch =
   
            let timeOut = case maybeMaxTime of
                    Just maxTime -> terminateTimeOut maxTime proofSearch
                    Nothing -> False
                stepLimit = case maybeMaxSteps of
                    Just maxSteps -> terminateStepLimit maxSteps proofSearch
                    Nothing -> False
            in timeOut || stepLimit