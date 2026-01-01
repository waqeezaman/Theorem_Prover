module Resolution where
import FOL ( Literal(..) )
import Unification (Sub, applySubToClause, applySubToLiteral, unifyingPairs)
import Utils (uniquePairsBetweenLists)

opposingPolarityPairs :: [(Literal, Literal)] -> [(Literal, Literal)]
opposingPolarityPairs [] = []
opposingPolarityPairs ((a,b): xs) = case (a, b) of
    (Pos _, Neg _) -> (a,b): opposingPolarityPairs xs
    (Neg _, Pos _) -> (a,b): opposingPolarityPairs xs
    _ -> opposingPolarityPairs xs

-- Returns a set of clauses that have been derived using resolution 
resolve :: [Literal] -> [Literal] -> [[Literal]]
resolve clause1 clause2 = 
    map (applyResolution clause1 clause2) pairs  
    where pairs = unifyingPairs (opposingPolarityPairs (uniquePairsBetweenLists clause1 clause2))

-- Applies the resolution step to two clauses 
-- Given a substitution that unifies them, and the two literals that will be cancelled out 
applyResolution :: [Literal] -> [Literal] -> (Literal,Literal, Sub) -> [Literal]
applyResolution clause1 clause2 (literal1, literal2, sub) = 
        resolvedClause
    where 
        resolvedClause = [literal | literal <- joinedClause , literal /= subbedLiteral1 && literal /= subbedLiteral2 ]
        joinedClause = subbedClause1 ++ subbedClause2 
        subbedClause1 = applySubToClause sub clause1 
        subbedClause2 = applySubToClause sub clause2 
        subbedLiteral1 = applySubToLiteral sub literal1 
        subbedLiteral2 = applySubToLiteral sub literal2 