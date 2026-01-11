{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Utils.IsTautologyTests (runIsTautologyTests) where

import FOL ( Clause(Clause), Literal(Pos, Neg), Predicate(R) )
import Utils (isTautology)

p = Pos (R ("P", []))
notP = Neg (R ("P", []))
q = Pos (R ("Q", []))
notQ = Neg (R ("Q", []))
r = Pos (R ("R", []))

clause1 = Clause [p, notP]
clause2 = Clause [p, q]
clause3 = Clause [q, r, notP, p]
clause4 = Clause []
clause5 = Clause [p, notQ, r]
clause6 = Clause [p, q, notP]

test1 = isTautology clause1
test2 = not (isTautology clause2)
test3 = isTautology clause3
test4 = not (isTautology clause4)
test5 = not (isTautology clause5)
test6 = isTautology clause6

runIsTautologyTests = concat
    [ "\n\n Running Is Tautology Tests"
    , "\n Test 1: " ++ show test1
    , "\n Test 2: " ++ show test2
    , "\n Test 3: " ++ show test3
    , "\n Test 4: " ++ show test4
    , "\n Test 5: " ++ show test5
    , "\n Test 6: " ++ show test6
    ]