{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}


module Config where
import PassiveQueue ( PassiveQueueConfig(..), PassiveQueueType(Weight, Age) ) 
import Filtering ( FilteringType(..) )
import GHC.Generics (Generic)
import Data.Aeson ( FromJSON, eitherDecodeFileStrict' )


data Config = Config
    {
        filterFunction :: [FilteringType],
        stopAfterNSteps :: Maybe Int,
        passiveQueues :: [PassiveQueueConfig]
    } deriving (Generic, FromJSON)


defaultConfig :: Config
defaultConfig = Config 
    {
        filterFunction = [RemoveTautologies, ForwardSubsumption],
        stopAfterNSteps = Nothing, 
        passiveQueues = [
            PQConfig{
                weightConfig = 10,
                pqTypeConfig = Age
            },
            PQConfig {
                weightConfig = 1,
                pqTypeConfig = Weight
            }
        ]
    }


loadConfig :: FilePath -> IO Config
loadConfig path = do
  result <- eitherDecodeFileStrict' path
  case result of
    Left err   -> fail err
    Right config -> return config

