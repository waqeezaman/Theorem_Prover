-- useful utils to add 
-- alpha equivalencee 
-- pushing connectives to the right 
-- e.g. (A AND B) AND C  -> A AND (B AND C)
-- gives us a standardised way to deal with connectives 
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Utils (transitiveClosure, fromCNFToClausalForm, disjunctionToLiteralList) where 

import qualified Data.Map as Map
import FOL

-- Returns the transitive closure of a Map
transitiveClosure :: Ord k => Map.Map k k -> Map.Map k k
transitiveClosure sub = Map.map (transitiveClosure' sub) sub

transitiveClosure' :: Ord t => Map.Map t t -> t -> t
transitiveClosure' map x =
    case mapping of 
        Just t -> transitiveClosure' map t 
        Nothing -> x
    where mapping = Map.lookup x map


fromCNFToClausalForm :: Formula -> [[Literal]]
fromCNFToClausalForm formula = case formula of 
    (Atom (R (p, terms))) -> [[Pos( R( p, terms))]]
    (Not(Atom (R (p, terms)))) -> [[Neg( R( p, terms))]] 
    (p `Or` q) -> [disjunctionToLiteralList (p `Or` q)]
    (p `And` q) ->  fromCNFToClausalForm p ++ fromCNFToClausalForm q
    _ -> error "Expected CNF"  


-- fromCNFToClausalForm (Atom (R (p, terms))) = [[Pos( R( p, terms))]]
-- fromCNFToClausalForm (Not(Atom (R (p, terms)))) = [[Neg( R( p, terms))]] 
-- fromCNFToClausalForm (p `Or` q) = [disjunctionToLiteralList (p `Or` q)]
-- fromCNFToClausalForm (p `And` q) =  fromCNFToClausalForm p ++ fromCNFToClausalForm q
-- fromCNFToClausalForm _ = error "Expected CNF"  


disjunctionToLiteralList :: Formula -> [Literal]
disjunctionToLiteralList formula = case formula of 
    (p `Or` q) -> disjunctionToLiteralList p ++ disjunctionToLiteralList q
    (Not (Atom(R (p, terms)))) -> [Neg (R (p, terms))] 
    (Atom(R (p, terms))) -> [Pos (R (p, terms))] 
    _ -> error "Expected a disjunction"  

-- disjunctionToLiteralList (p `Or` q) = disjunctionToLiteralList p ++ disjunctionToLiteralList q
-- disjunctionToLiteralList (Not (Atom(R (p, terms)))) = [Neg (R (p, terms))] 
-- disjunctionToLiteralList (Atom(R (p, terms))) = [Pos (R (p, terms))] 
-- disjunctionToLiteralList _ = error "Expected a disjunction"  