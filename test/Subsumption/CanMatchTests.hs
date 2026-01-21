{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.CanMatchTests (runCanMatchTests) where

import FOL (Clause(..), Literal(..), Predicate(..), Term(..))
import Subsumption.Subsumption (canMatch)

varX   = Var "X"
varY   = Var "Y"
constA = Fn ("a", [])
constB = Fn ("b", [])
pX = Pos (R ("P", [varX]))
pY = Pos (R ("P", [varY]))
pA = Pos (R ("P", [constA]))
pB = Pos (R ("P", [constB]))
qX = Pos (R ("Q", [varX]))
qA = Pos (R ("Q", [constA]))
qB = Pos (R ("Q", [constB]))
negQA = Neg (R ("Q", [constA]))

test1 = canMatch (Clause [pA]) (Clause [pA, qA])

test2 = canMatch (Clause [pX]) (Clause [pA, qA])

test3 = canMatch (Clause [pX, qX]) (Clause [pA, qA])

test4 = not $ canMatch (Clause [pX, qX]) (Clause [pA, qB])

test5 = canMatch (Clause [pX, qX]) (Clause [pA, pB, qB])

test6 = canMatch (Clause [pX, pY]) (Clause [pA])

test7 = not $ canMatch (Clause [qX]) (Clause [negQA])

runCanMatchTests = concat
    [ 
        "\n\n Running Can Match Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5,
        "\n Test 6: " ++ show test6,
        "\n Test 7: " ++ show test7
    ]