{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.MatchPredicatesTests (runMatchPredicatesTests) where

import qualified Data.Map as Map
import FOL (Predicate(..), Term(..))
import Subsumption.Subsumption (matchPredicates)

varX = Var "X"
constA = Fn ("a", [])
constB = Fn ("b", [])

-- P(X)
predPX = R ("P", [varX])
-- P(a)
predPA = R ("P", [constA])
-- Q(a)
predQA = R ("Q", [constA])
-- P(a, b)
predPAB = R ("P", [constA, constB])

test1 = case matchPredicates predPX predPA Map.empty of
    Just sub -> Map.lookup varX sub == Just constA
    Nothing  -> False

test2 = case matchPredicates predPA predQA Map.empty of
    Nothing -> True
    Just _  -> False

test3 = case matchPredicates predPA predPAB Map.empty of
    Nothing -> True
    Just _  -> False

subA = Map.fromList [(varX, constA)]
test4 = case matchPredicates predPX (R ("P", [constB])) subA of
    Nothing -> True
    Just _  -> False

runMatchPredicatesTests = concat
    [ 
        "\n\n Running Match Predicates Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4
    ]