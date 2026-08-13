{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}

module Config where

import PassiveQueue ( PassiveQueueConfig(..), PassiveQueueType(Weight, Age) ) 
import Filtering ( FilteringType(..) )
import GHC.Generics (Generic)
import Data.Aeson ( FromJSON , eitherDecodeFileStrict' )

-- The config for the entire proof search 
-- Defines the total time limit allowed for the proof search 
-- As well as a schedule of startegies to try
data ProofSearchConfig = ProofSearchConfig 
    {
        totalTimeLimit :: Maybe Int,
        threads :: Int,
        schedule :: Schedule
    } deriving (Generic, FromJSON)

-- The options for a single proof search strategy
data SingleProofSearchOptions =  SingleProofSearchOptions
    {
        filterFunction :: [FilteringType], 
        stopAfterNSteps :: Maybe Int,
        passiveQueues :: [PassiveQueueConfig],
        timeLimit :: Maybe Double
    } deriving (Generic, FromJSON)

newtype Schedule = Schedule [SingleProofSearchOptions] 
    deriving stock ( Generic )
    deriving newtype ( FromJSON )
 

loadProofSearchConfig :: FilePath -> IO ProofSearchConfig
loadProofSearchConfig path = do  
  result <- eitherDecodeFileStrict' path
  case result of
    Left err   -> fail err
    Right config -> return config

defaultProofSearchConfig :: ProofSearchConfig 
defaultProofSearchConfig = ProofSearchConfig 
    {
        totalTimeLimit = Just 30,
        threads = 2,
        schedule = Schedule [
            SingleProofSearchOptions {
                filterFunction = [RemoveTautologies, ForwardSubsumption],
                stopAfterNSteps = Nothing,
                passiveQueues = [
                    PQConfig{
                        weightConfig = 1,
                        pqTypeConfig = Age
                    },
                    PQConfig {
                        weightConfig = 10,
                        pqTypeConfig = Weight
                    }
                ],
                timeLimit = Nothing
            },
            SingleProofSearchOptions {
                filterFunction = [RemoveTautologies, ForwardSubsumption],
                stopAfterNSteps = Nothing,
                passiveQueues = [
                    PQConfig{
                        weightConfig = 5,
                        pqTypeConfig = Age
                    },
                    PQConfig {
                        weightConfig = 10,
                        pqTypeConfig = Weight
                    }
                ],
                timeLimit = Nothing
            }
        ]
    }





