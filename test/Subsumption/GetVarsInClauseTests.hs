{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.GetVarsInClauseTests (runGetVarsInClauseTests) where


import FOL (Clause(..), Literal(..), Predicate(..), Term(..))
import Subsumption.Subsumption (getVarsInClause)
import Data.List (sort)

clause1 = Clause [Pos (R ("P", [Fn ("a", []), Fn ("b", [])]))]
expectedV1 = []

clause2 = Clause [Pos (R ("P", [Var "X", Var "Y"]))]
expectedV2 = ["X", "Y"]

clause3 = Clause [ Pos (R ("P", [Var "X"])), Pos (R ("Q", [Var "X"]))]
expectedV3 = ["X"]

clause4 = Clause [Pos (R ("P", [Fn ("f", [Fn ("g", [Var "Z"])])]))]
expectedV4 = ["Z"]

clause5 = Clause [ Pos (R ("P", [Var "X", Fn ("a", [])])), Neg (R ("Q", [Var "Y", Fn ("f", [Var "X"]) ] ))]
expectedV5 = ["X", "Y"]


testV1 = sort (getVarsInClause clause1) == sort expectedV1
testV2 = sort (getVarsInClause clause2) == sort expectedV2
testV3 = sort (getVarsInClause clause3) == sort expectedV3
testV4 = sort (getVarsInClause clause4) == sort expectedV4
testV5 = sort (getVarsInClause clause5) == sort expectedV5

runGetVarsInClauseTests = concat
    [ "\n\n Running Get Vars In Clause Tests",
      "\n Test 1: " ++ show testV1,
      "\n Test 2: " ++ show testV2,
      "\n Test 3: " ++ show testV3,
      "\n Test 4: " ++ show testV4,
      "\n Test 5: " ++ show testV5
    ]