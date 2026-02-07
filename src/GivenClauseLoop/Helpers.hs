{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# HLINT ignore "Use null" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE OverloadedRecordDot #-}

module GivenClauseLoop.Helpers where

import Prelude hiding (id)
import FOL ( Clause(..) )
import GivenClauseLoop.Types
    ( DerivedClause(Axiom, derived, clauseId) )

createAxioms :: [Clause] -> [DerivedClause]
createAxioms clauses =
    zipWith (\ clause i -> Axiom {derived = clause, clauseId = i}) clauses [1..]


-- Returns True if the empty clause is contained in the list 
derivedFalse :: [DerivedClause] -> Bool
derivedFalse = foldr (\ x -> (||) (x.derived == Clause [])) False

derivedFalseClause :: [DerivedClause] -> Maybe DerivedClause
derivedFalseClause [] = Nothing
derivedFalseClause (x:xs) = if x.derived == Clause [] then Just x
                            else derivedFalseClause xs

