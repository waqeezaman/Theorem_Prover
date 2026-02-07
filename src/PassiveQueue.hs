{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module PassiveQueue where

import qualified Data.PQueue.Prio.Min as PQ
import GivenClauseLoop.Types ( DerivedClause(clauseId, derived) )
import Control.Lens ( (&), (^.), (.~), makeLenses )
import FOL (getLiterals)
import Data.Aeson (FromJSON)
import GHC.Generics (Generic)

data PassiveQueueType = Age | Weight deriving (Generic, FromJSON, Show)

data PassiveQueue = PassiveQueue
    {
        _pqType :: PassiveQueueType,
        _queue :: PQ.MinPQueue Int DerivedClause,
        _ordering :: DerivedClause -> Int,
        _weight :: Int
    }

makeLenses ''PassiveQueue


instance Show PassiveQueue where
    show :: PassiveQueue -> String
    show pq = 
        let 
            header = "Queue Type: " ++ show (pq ^. pqType) ++ 
                     " (Weight: " ++ show (pq ^. weight) ++ ")\n"
            
            items = PQ.toAscList (pq ^. queue)
            formatItem (priority, clause) = "  [Priority " ++ show priority ++ "] " ++ show clause
            body = unlines (map formatItem items)
        in header ++ body

    
data PassiveQueueConfig = PQConfig {
        pqTypeConfig :: PassiveQueueType,
        weightConfig :: Int
    } deriving (Generic, FromJSON)


pqConfigToPQ :: PassiveQueueConfig -> PassiveQueue
pqConfigToPQ config =
    PassiveQueue
    {
        _queue = PQ.Empty,
        _weight = config.weightConfig,
        _pqType = config.pqTypeConfig,
        _ordering = pqTypeToOrderingFunction  config.pqTypeConfig
    }

pqTypeToOrderingFunction :: PassiveQueueType -> (DerivedClause -> Int)
pqTypeToOrderingFunction pqType = case pqType of
    Age -> orderByAge
    Weight -> orderByWeight


createPassiveQueue :: PassiveQueueType -> Int -> PassiveQueue
createPassiveQueue pqType weight = PassiveQueue
    {
        _pqType = pqType,
        _ordering = pqTypeToOrderingFunction pqType,
        _weight = weight,
        _queue = PQ.Empty
    }

addToPassiveQueue :: PassiveQueue -> DerivedClause -> PassiveQueue
addToPassiveQueue pq newClause =
    pq & queue .~ PQ.insert (pq ^. ordering $ newClause) newClause (pq ^. queue)


orderByAge :: DerivedClause -> Int
orderByAge clause = clause.clauseId

orderByWeight :: DerivedClause -> Int
orderByWeight clause = length $ getLiterals clause.derived
