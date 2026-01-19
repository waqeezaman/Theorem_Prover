-- Functions to solve a problem 
-- Using a clause selection strategy that 
-- Uses a ratio between age and weight

{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DataKinds #-}

module GivenClauseLoop.RatioSolver where

import GivenClauseLoop.Types (DerivedClause (..), ProofSearchState, ProofSearch (..))
import Utils (isTautology)
import FOL (getLiterals, Literal)
import Data.List (sortOn)
import GivenClauseLoop.Helpers (resolutionWithDerivedClauses, factorisingWithDerivedClause, derivedFalseClause)
import Data.Maybe (isJust)
import qualified GHC.Records

data RatioPassiveSets = RatioPassiveSets
    { byWeight :: [DerivedClause]
    , byAge    :: [DerivedClause]
    }

createRatioPassiveSets :: [DerivedClause] -> RatioPassiveSets
createRatioPassiveSets clauses =
    RatioPassiveSets{byAge = clauses, byWeight = sortedByWeight}
    where
        sortedByWeight = sortOn (length . getLiterals . derived) clauses
 

givenClauseLoopRatio :: Int -> Int -> RatioPassiveSets -> [DerivedClause] -> ProofSearchState (Maybe DerivedClause)
givenClauseLoopRatio _ _ RatioPassiveSets{byWeight=[], byAge = []} _ = return Nothing
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


givenClauseLoopRatioProofSearch :: Int -> Int -> Int -> RatioPassiveSets -> [DerivedClause] -> ProofSearchState ProofSearch
givenClauseLoopRatioProofSearch _ _ _ RatioPassiveSets{byWeight=[], byAge = []} actives = return Search {isUnsat = Just False, passives = [], actives = actives}
givenClauseLoopRatioProofSearch 0 _ _ passives actives = 
    return Search{isUnsat = Nothing, passives = passives.byAge, actives = actives}
givenClauseLoopRatioProofSearch k n ratio passives actives =
        let (selected, unselectedPassives) = selectByRatio n ratio passives in
        do
            factored <- factorisingWithDerivedClause selected
            resolved <- concat <$> mapM (resolutionWithDerivedClauses selected) actives
            let derivedClauses = filter (not . isTautology . derived) (factored ++ resolved)
            let newPassives = addDerivedToPassives derivedClauses unselectedPassives
            let newActives = selected : actives
            let unsat = derivedFalseClause derivedClauses
            if isJust unsat then return Search{isUnsat = Just True, passives = newPassives.byAge, actives = newActives}
            else givenClauseLoopRatioProofSearch (k-1) (n+1) ratio newPassives newActives

-- Decides whether to select a clause using age or weight
selectByRatio :: Int -> Int -> RatioPassiveSets -> (DerivedClause, RatioPassiveSets)
selectByRatio steps ratio passives
    | steps `mod` ratio == 0  =
        let (x, xs) = pickOldest (byAge passives)
        in (x, RatioPassiveSets { byAge = xs, byWeight = deleteFromList x passives.byWeight })
    | otherwise =
        let (x, xs) = pickLightest (byWeight passives)
        in (x,  RatioPassiveSets { byAge = deleteFromList x passives.byAge, byWeight = xs })


-- Adds new clauses into both lists and keeps them sorted
addDerivedToPassives :: [DerivedClause] -> RatioPassiveSets -> RatioPassiveSets
addDerivedToPassives new passives = RatioPassiveSets
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


-- -- Note -- currently the axioms may directly infer the empty clause 
-- -- In this set up we must wait for the empty clause to then later be selected during the given clause loop
-- -- Might be worth looking into immediately returning false if the empty clause is derived 
activateAxioms :: [DerivedClause] -> [DerivedClause] -> [DerivedClause] -> ProofSearchState [DerivedClause] 
activateAxioms axioms actives passives = case axioms of
    [] -> return passives
    (x:xs) -> 
        do  
            factored <- factorisingWithDerivedClause x 
            resolved <- concat <$> mapM (resolutionWithDerivedClauses x) actives 
            let derivedClauses = filter (not . isTautology . derived) (factored ++ resolved)
            let newPassives = passives ++ derivedClauses
            let newActives = x : actives
            activateAxioms xs newActives newPassives
            