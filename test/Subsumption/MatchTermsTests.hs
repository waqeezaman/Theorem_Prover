{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.MatchTermsTests where

import qualified Data.Map as Map
import FOL (Term(..))
import Subsumption.Subsumption (matchTerms)

varX = Var "X"
varY = Var "Y"
constA = Fn ("a", [])
constB = Fn ("b", [])
fA = Fn ("f", [constA])
fB = Fn ("f", [constB])

test1 = case matchTerms [varX, varY] [constA, constB] Map.empty of
    Just sub -> Map.lookup varX sub == Just constA && 
                Map.lookup varY sub == Just constB
    Nothing  -> False

test2 = case matchTerms [varX, varX] [constA, constA] Map.empty of
    Just sub -> Map.lookup varX sub == Just constA
    Nothing  -> False

test3 = case matchTerms [varX, varX] [constA, constB] Map.empty of
    Nothing -> True
    Just _  -> False

test4 = case matchTerms [varX] [constA, constB] Map.empty of
    Nothing -> True
    Just _  -> False

test5 = case matchTerms [Fn ("f", [varX]), varX] [fA, constA] Map.empty of
    Just sub -> Map.lookup varX sub == Just constA
    Nothing  -> False

test6 = case matchTerms [Fn ("f", [varX]), varX] [fA, constB] Map.empty of
    Nothing  -> True
    Just _ -> False

runMatchTermsTests = concat
    [ 
        "\n\n Running Match Terms Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5,
        "\n Test 6: " ++ show test6
    ]