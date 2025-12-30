{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Unification.ApplySubToTermsTests where 
import FOL (Term(..))
import qualified Data.Map as Map
import Unification (applySubToTerms)


t1 = Var "X"
t2 = Var "Y"
t3 = Fn("F", [t1])
t4 = Fn("F", [Fn("G", [t2]), t1])


terms1 = []
terms2 = [t1]
terms3 = [t3]
terms4 = [t4]
terms5 = [t1,t2]
terms6 = [t3, t4]
terms7 = [t1,t2,t3,t4]


sub = Map.fromList [(t1, Fn("A", [])), (t2, Fn("B", []))]

subbedT1 = Fn("A", [])
subbedT2 = Fn("B", [])
subbedT3 = Fn("F", [subbedT1])
subbedT4 = Fn("F", [Fn("G", [subbedT2]), subbedT1])


test1 = applySubToTerms sub terms1 == terms1
test2 = applySubToTerms sub terms2 == [subbedT1]
test3 = applySubToTerms sub terms3 == [subbedT3]
test4 = applySubToTerms sub terms4 == [subbedT4]
test5 = applySubToTerms sub terms5 == [subbedT1, subbedT2]
test6 = applySubToTerms sub terms6 == [subbedT3, subbedT4] 
test7 = applySubToTerms sub terms7 == [subbedT1, subbedT2, subbedT3, subbedT4]

runApplySubToTermsTests = concat 
    [
        "\n\n Running Apply Sub To Terms Tests", 
        "\n Test 1: " ++ show test1, 
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5,
        "\n Test 6: " ++ show test6,
        "\n Test 7: " ++ show test7
    ]