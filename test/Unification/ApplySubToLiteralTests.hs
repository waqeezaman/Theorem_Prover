{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Unification.ApplySubToLiteralTests (runApplySubToLiteralTests) where 
import FOL ( Literal(Pos, Neg), Predicate(R), Term(Fn, Var) )
import qualified Data.Map as Map
import Unification (applySubToLiteral)
    

t1 = Var "X"
t2 = Var "Y"
t3 = Fn("F", [t1, t2])
t4 = Fn("G", [Fn("F", [t3, t1])])


literal1 = Pos (R("P", [t1]))

literal2 = Neg (R("Q", [t2]))

literal3 = Pos (R("R", [t3]))

literal4 = Neg (R("S", [t4]))

literal5 = Neg (R("T", [t1, t2, t3, t4]))


sub = Map.fromList [(Var "X", Fn("A", [])), (Var "Y", Fn("B", []))]


subbedT1 = Fn("A", [])
subbedT2 = Fn("B", [])

subbedT3 = Fn("F", [subbedT1, subbedT2])
subbedT4 = Fn("G", [Fn("F", [subbedT3, subbedT1])])


test1 = applySubToLiteral sub literal1 == Pos(R("P", [subbedT1]))
test2 = applySubToLiteral sub literal2 == Neg(R("Q", [subbedT2]))
test3 = applySubToLiteral sub literal3 == Pos(R("R", [subbedT3]))
test4 = applySubToLiteral sub literal4 == Neg(R("S", [subbedT4]))
test5 = applySubToLiteral sub literal5 == Neg(R("T", [subbedT1, subbedT2, subbedT3, subbedT4]))


runApplySubToLiteralTests = concat 
    [
        "\n\n Running Apply Sub To Literal Tests", 
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5
    ]

