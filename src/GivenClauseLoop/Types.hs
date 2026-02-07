{-# LANGUAGE DeriveAnyClass #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# HLINT ignore "Use null" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

module GivenClauseLoop.Types where

import FOL (Clause)
import Data.Aeson (ToJSON (toJSON), object, KeyValue ((.=)))
import GHC.Generics (Generic)


data Step = Resolution | Factorisation deriving (Show, Generic, ToJSON)

data DerivedClause =
    Derived {
        derived :: Clause,
        parent1 :: DerivedClause,
        parent2 :: DerivedClause,
        step :: Step,
        clauseId :: Int
        }
    | Axiom {derived :: Clause, clauseId:: Int}
    deriving (Show, Generic)

instance ToJSON DerivedClause where
    toJSON (Axiom c cid) = object
        [ 
            "id" .= cid,
            "clause" .= c,
            "type" .= ("Axiom" :: String)
        ]
    toJSON (Derived d p1 p2 s cid) = object
        [
            "id" .= cid,
            "clause" .= d,
            "type" .= s,
            "parent1" .= p1.clauseId,
            "parent2" .= p2.clauseId
        ]
