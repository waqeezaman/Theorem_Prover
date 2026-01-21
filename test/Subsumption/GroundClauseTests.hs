{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.GroundClauseTests (runGroundClauseTests) where

import FOL (Clause(..), Literal(..), Predicate(..), Term(..))
import Subsumption.Subsumption (groundClause)

clause1 = Clause [Pos (R ("P", [Var "X"]))]
expectedClause1 = Clause [Pos (R ("P", [Fn ("_G_X" ,[])]))]

clause2 = Clause [Pos (R ("P", [Var "X", Fn ("a", []), Var "Y"]))]
expectedClause2 = Clause [Pos (R ("P", [Fn ("_G_X", []), Fn ("a", []), Fn ("_G_Y", [])]))]

clause3 = Clause [Pos (R ("P", [Var "X"])), Pos (R ("Q", [Var "X"]))]
expectedClause3 = Clause [Pos (R ("P", [Fn ("_G_X", [])])), Pos (R ("Q", [Fn ("_G_X", [])]))]

clause4 = Clause [Pos (R ("P", [Fn ("f", [Var "X"])]))]
expectedClause4 = Clause [Pos (R ("P", [Fn ("f", [Fn ("_G_X", [])])]))]

clause5 = Clause [Neg (R ("P", [Var "X"]))]
expectedClause5 = Clause [Neg (R ("P", [Fn ("_G_X", [])]))]

clause6 = Clause []
expectedClause6 = Clause []

test1 = groundClause clause1 == expectedClause1
test2 = groundClause clause2 == expectedClause2
test3 = groundClause clause3 == expectedClause3
test4 = groundClause clause4 == expectedClause4
test5 = groundClause clause5 == expectedClause5
test6 = groundClause clause6 == expectedClause6


runGroundClauseTests = concat
    [ 
        "\n\n Running Clause Grounding Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5,
        "\n Test 6: " ++ show test6
    ]