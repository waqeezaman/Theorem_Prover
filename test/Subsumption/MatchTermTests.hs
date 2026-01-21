{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.MatchTermTests (runMatchTermTests) where

import qualified Data.Map as Map
import FOL (Term(..))
import Subsumption.Subsumption (matchTerm)

varX = Var "X"
constA = Fn ("a", [])
constB = Fn ("b", [])
fX = Fn ("f", [varX])
fA = Fn ("f", [constA])
gA = Fn ("g", [constA])

test1 = case matchTerm varX constA Map.empty of
    Just sub -> Map.lookup varX sub == Just constA
    Nothing  -> False

subA  = Map.fromList [(varX, constA)]
test2 = case matchTerm varX constA subA of
    Just sub -> sub == subA
    Nothing  -> False

test3 = case matchTerm varX constB subA of
    Nothing -> True
    Just _  -> False

test4 = case matchTerm constA constA Map.empty of
    Just sub -> sub == Map.empty
    Nothing  -> False

test5 = case matchTerm constA constB Map.empty of
    Nothing -> True
    Just _  -> False

test6 = case matchTerm fX fA Map.empty of
    Just sub -> Map.lookup varX sub == Just constA
    Nothing  -> False

test7 = case matchTerm fA gA Map.empty of
    Nothing -> True
    Just _  -> False

runMatchTermTests = concat
    [ 
        "\n\n Running Match Term Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5,
        "\n Test 6: " ++ show test6,
        "\n Test 7: " ++ show test7
    ]