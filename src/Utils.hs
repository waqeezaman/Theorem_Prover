-- useful utils to add 
-- alpha equivalencee 
-- pushing connectives to the right 
-- e.g. (A AND B) AND C  -> A AND (B AND C)
-- gives us a standardised way to deal with connectives 
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Utils (
    transitiveClosure,
    fromCNFToClausalForm,
    disjunctionToLiteralList,
    literalToPredicate,
    removeFirstOccurenceFromClause,
    uniquePairs,
    makeSetOfSets,
    uniquePairsBetweenLists,
    isTautology
    ) where

import qualified Data.Map as Map
import FOL
    ( Literal(..), Formula(Atom, And, Or, Not), Predicate(R), Clause (..) )
import qualified Data.Set as Set


-- Returns the transitive closure of a Map
transitiveClosure :: Ord k => Map.Map k k -> Map.Map k k
transitiveClosure sub = Map.map (transitiveClosure' sub) sub

transitiveClosure' :: Ord t => Map.Map t t -> t -> t
transitiveClosure' map x =
    case mapping of
        Just t -> transitiveClosure' map t
        Nothing -> x
    where mapping = Map.lookup x map


-- Converts a formula in CNF to clausal form 
-- Returns a list of list of literals 
-- Where each list of literals is a disjunction 
fromCNFToClausalForm :: Formula -> [[Literal]]
fromCNFToClausalForm formula = case formula of
    (Atom (R (p, terms))) -> [[Pos ( R ( p, terms))]]
    (Not(Atom (R (p, terms)))) -> [[Neg ( R ( p, terms))]]
    (p `Or` q) -> [disjunctionToLiteralList (p `Or` q)]
    (p `And` q) ->  fromCNFToClausalForm p ++ fromCNFToClausalForm q
    _ -> error "Expected CNF"

-- Takes a formula in disjunctive normal form 
-- And returns a list of literals representing the same disjunction  
disjunctionToLiteralList :: Formula -> [Literal]
disjunctionToLiteralList formula = case formula of
    (p `Or` q) -> disjunctionToLiteralList p ++ disjunctionToLiteralList q
    (Not (Atom(R (p, terms)))) -> [Neg (R (p, terms))]
    (Atom(R (p, terms))) -> [Pos (R (p, terms))]
    _ -> error "Expected a disjunction"

-- Extracts the predicate from a literal 
-- Removes the polarity indicator
literalToPredicate :: Literal -> Predicate
literalToPredicate (Pos p) = p
literalToPredicate (Neg p) = p


-- Removes the first occurence of a literal from a clause 
removeFirstOccurenceFromClause :: [Literal] -> Literal -> [Literal]
removeFirstOccurenceFromClause = removeFirstOccurenceFromClause' []

removeFirstOccurenceFromClause' :: [Literal] -> [Literal] -> Literal -> [Literal]
removeFirstOccurenceFromClause' prefix [] _ = prefix
removeFirstOccurenceFromClause' prefix (x:xs) l =
    if x == l
    then prefix ++ xs
    else removeFirstOccurenceFromClause' (prefix ++ [x]) xs l


-- Given a list of elements returns a list of pairs 
-- Containing only unique pairs, i.e. [a,b] -> [(a,b)] and would not return the pair (b,a)
uniquePairs :: [a] -> [(a, a)]
uniquePairs [] = []
uniquePairs (x:xs) = [(x, y) | y <- xs] ++ uniquePairs xs

uniquePairsBetweenLists :: [a] -> [b] -> [(a,b)]
uniquePairsBetweenLists [] _ = []
uniquePairsBetweenLists (x:xs) ys = [(x,y) | y <- ys] ++ uniquePairsBetweenLists xs ys


makeSetOfSets :: Ord a => [[a]] -> Set.Set (Set.Set a)
makeSetOfSets list = Set.fromList (map Set.fromList list)

isTautology :: Clause -> Bool
isTautology (Clause lits) = 
    let (posAtoms, negAtoms) = foldr split (Set.empty, Set.empty) lits
    in not $ Set.disjoint posAtoms negAtoms
  where
    split (Pos a) (ps, ns) = (Set.insert a ps, ns)
    split (Neg a) (ps, ns) = (ps, Set.insert a ns)