module GivenClauseLoop.Timing where

import Control.Lens ( (.=) )
import Control.Monad.State ( MonadIO(liftIO) )


import GivenClauseLoop.State (ProofSearchState, timeElapsed)
import Data.Time.Clock.System
    ( getSystemTime, SystemTime(MkSystemTime) )


updateTimeElapsed :: SystemTime -> ProofSearchState ()
updateTimeElapsed startTime = do
    currentTime <- liftIO getSystemTime
    timeElapsed .= diffSystemTime currentTime startTime


-- Helper to calculate the difference in seconds
diffSystemTime :: SystemTime -> SystemTime -> Double
diffSystemTime (MkSystemTime s1 n1) (MkSystemTime s2 n2) =
    let seconds = fromIntegral (s1 - s2)
        nanos   = fromIntegral (n1 - n2) / 1e9
    in seconds + nanos
