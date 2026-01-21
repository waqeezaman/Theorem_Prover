{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.MatchLiteralsTests (runMatchLiteralsTests) where

import qualified Data.Map as Map
import FOL (Literal(..), Predicate(..), Term(..))
import Subsumption.Subsumption (matchLiterals)

varX = Var "X"
constA = Fn ("a", [])
predP = R ("P", [varX])
predPA = R ("P", [constA])
predQ = R ("Q", [varX])

test1 = case matchLiterals (Pos predP) (Pos predPA) Map.empty of
    Just sub -> Map.lookup varX sub == Just constA
    Nothing  -> False

test2 = case matchLiterals (Neg predP) (Neg predPA) Map.empty of
    Just sub -> Map.lookup varX sub == Just constA
    Nothing  -> False

test3 = case matchLiterals (Pos predP) (Neg predP) Map.empty of
    Nothing -> True
    Just _  -> False

test4 = case matchLiterals (Neg predP) (Pos predP) Map.empty of
    Nothing -> True
    Just _  -> False

test5 = case matchLiterals (Pos predP) (Pos predQ) Map.empty of
    Nothing -> True
    Just _  -> False

runMatchLiteralsTests = concat
    [ 
        "\n\n Running MatchLiterals Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5
    ]