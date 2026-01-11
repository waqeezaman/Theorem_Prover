-- Functions to solve a problem 
-- Using a clause selection strategy that 
-- Uses a ratio between age and weight

{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DataKinds #-}

module GivenClauseLoop.RatioSolver where

import GivenClauseLoop.Types (DerivedClause (..), ProofSearchState)
import Utils (isTautology)
import FOL (getLiterals)
import Data.List (sortOn)
import GivenClauseLoop.Helpers (resolutionWithDerivedClauses, factorisingWithDerivedClause, derivedFalseClause)
import Data.Maybe (isJust)
import qualified GHC.Records

data PassiveSets = PassiveSets
    { byWeight :: [DerivedClause] 
    , byAge    :: [DerivedClause] 
    }

givenClauseLoopRatio :: Int -> Int -> PassiveSets -> [DerivedClause] -> ProofSearchState (Maybe DerivedClause)
givenClauseLoopRatio _ _ PassiveSets{byWeight=[], byAge = []} _ = return Nothing
givenClauseLoopRatio n ratio passives actives =
        let (selected, unselectedPassives) = selectByRatio n ratio passives in
        do
            factored <- factorisingWithDerivedClause selected
            resolved <- concat <$> mapM (resolutionWithDerivedClauses selected) actives
            let derivedClauses = filter (not . isTautology . derived) (factored ++ resolved)
            let newPassives = addDerivedToPassives derivedClauses unselectedPassives
            let newActives = selected : actives
            let unsat = derivedFalseClause derivedClauses
            if isJust unsat then return unsat
            else givenClauseLoopRatio (n+1) ratio newPassives newActives

-- Decides whether to select a clause using age or weight
selectByRatio :: Int -> Int -> PassiveSets -> (DerivedClause, PassiveSets)
selectByRatio steps ratio passives
    | steps `mod` ratio == 0  =
        let (x, xs) = pickOldest (byAge passives)
        in (x, PassiveSets { byAge = xs, byWeight = deleteFromList x passives.byWeight })
    | otherwise =
        let (x, xs) = pickLightest (byWeight passives)
        in (x,  PassiveSets { byAge = deleteFromList x passives.byAge, byWeight = xs })


-- Adds new clauses into both lists and keeps them sorted
addDerivedToPassives :: [DerivedClause] -> PassiveSets -> PassiveSets
addDerivedToPassives new passives = PassiveSets
    {
        byWeight = sortOn (length . getLiterals . derived) (passives.byWeight ++ new),
        byAge    = sortOn clauseId (passives.byAge ++ new)
    }

pickLightest :: [a] -> (a, [a])
pickLightest (x:xs) = (x, xs)
pickLightest [] = error "Attempting to pick lightest clause from empty set"

pickOldest :: [a] -> (a, [a])
pickOldest (x:xs) = (x, xs)
pickOldest [] = error "Attempting to pick oldest clause from empty set"

deleteFromList :: (Eq a, GHC.Records.HasField "clauseId" r1 a,  GHC.Records.HasField "clauseId" r2 a) => r2 -> [r1] -> [r1]
deleteFromList target = filter (\c -> c.clauseId /= target.clauseId)