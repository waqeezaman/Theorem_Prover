module Factoring where
import FOL ( Literal(..) )
import Unification
    ( Sub, applySubToClause, applySubToLiteral, unifyingPairs )
import Utils (removeFirstOccurenceFromClause, uniquePairs)


-- Takes a list of pairs of literals 
-- Returns a list containing only literals that have the same polarity 
samePolarityPairs :: [(Literal, Literal)] -> [(Literal, Literal)]
samePolarityPairs [] = []
samePolarityPairs ((a,b): xs) = case (a, b) of
    (Pos _, Pos _) -> (a,b): samePolarityPairs xs
    (Neg _, Neg _) -> (a,b): samePolarityPairs xs
    _ -> samePolarityPairs xs

-- for each pair 
-- apply the substitution to the clause and one of the literals
-- remove the subbed literal from the clause   
applyFactorisation :: [Literal] -> (Literal, Literal, Sub) -> [Literal]
applyFactorisation clause (l1, _, sub) = removeFirstOccurenceFromClause subbedClause subbedLiteral
    where
        subbedClause = applySubToClause sub clause
        subbedLiteral = applySubToLiteral sub l1

-- Factorise a clause
-- Removes literals of the same polarity that unify 
factorise :: [Literal] -> [[Literal]]
factorise literals  = case literals of 
    [] -> []
    [_] -> []
    _  -> map (applyFactorisation literals) pairs 
    where  
        pairs = unifyingPairs (samePolarityPairs (uniquePairs literals))

