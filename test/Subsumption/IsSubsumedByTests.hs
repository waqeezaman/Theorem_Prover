{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.IsSubsumedByTests where

import FOL (Clause(..), Literal(..), Predicate(..), Term(..))
import Subsumption.Subsumption (isSubsumedBy)

varX = Var "X"
constA = Fn ("a", [])
constB = Fn ("b", [])
pX = Pos (R ("P", [varX]))
pA = Pos (R ("P", [constA]))
pB = Pos (R ("P", [constB]))

test1 = isSubsumedBy (Clause [pX]) (Clause [pA])

test2 = not $ isSubsumedBy (Clause [pA]) (Clause [pX])

c3 = Clause [Pos (R ("P", [Fn ("f", [varX])]))]
d3 = Clause [Pos (R ("P", [Fn ("f", [constA])])), Pos (R ("Q", [constB]))]
test3 = isSubsumedBy c3 d3

c4 = Clause [Pos (R ("P", [Var "X", Var "Y"]))]
d4 = Clause [Pos (R ("P", [Var "Y", Var "X"]))]
test4 = isSubsumedBy c4 d4

test5 = isSubsumedBy (Clause [pX]) (Clause [pX])

test6 = isSubsumedBy (Clause []) (Clause [pX])

runIsSubsumedByTests = concat
    [ 
        "\n\n Running IsSubsumedBy Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5,
        "\n Test 6: " ++ show test6
    ]