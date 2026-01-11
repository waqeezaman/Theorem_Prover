{-# LANGUAGE OverloadedRecordDot #-}

module HandleProof where
import GivenClauseLoop (DerivedClause (..))
import Data.List (nubBy, sortOn)
import Prelude hiding (id)

formatStep :: DerivedClause -> String
formatStep (Axiom c cid) =
    show cid ++ ": " ++ show c ++ " (Axiom)"
formatStep (Derived d p1 p2 s cid) =
    show cid ++ ": " ++ show d ++ " (" ++ show s ++ " of " ++ show p1.clauseId ++ ", " ++ show p2.clauseId ++ ")"


-- Recursively collect all clauses in the history
collectHistory :: DerivedClause -> [DerivedClause]
collectHistory a@(Axiom _ _) = [a]
collectHistory d@(Derived _ p1 p2 _ _) =
    d : collectHistory p1 ++ collectHistory p2

-- Clean up duplicates (same ID) and sort by ID
getLinearProof :: DerivedClause -> [DerivedClause]
getLinearProof goal =
    let allSteps = collectHistory goal
        uniqueSteps = nubBy (\a b -> a.clauseId == b.clauseId) allSteps
    in sortOn clauseId uniqueSteps


writeProofToFile :: FilePath -> Maybe DerivedClause -> IO ()
writeProofToFile _ Nothing = putStrLn "No Proof Found"
writeProofToFile path (Just goal) = do
    let proofSteps = getLinearProof goal
    let proofString = unlines (map formatStep proofSteps)
    writeFile path proofString
    putStrLn $ "Proof written to " ++ path