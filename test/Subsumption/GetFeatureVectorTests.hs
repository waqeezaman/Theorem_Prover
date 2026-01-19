{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.GetFeatureVectorTests (runGetFeatureVectorTests) where

import qualified Data.Map as Map
import FOL (Clause(..), Literal(..), Predicate(..), Term(..))
import Subsumption.SubsumptionFilter (getFeatureVector)

pP = "_P_P"
pQ = "_P_Q"
fA = "_F_a"
fB = "_F_b"
fF = "_F_f"
notPP = "_¬__P_P"


clause1 = Clause []
expectedFV1 = Map.empty

-- Test 2: Basic Unit Clause
-- P(a, b) -> {_P_P: 1, _F_a: 1, _F_b: 1}
clause2 = Clause [Pos (R ("P", [Fn ("a", []), Fn ("b", [])]))]
expectedFV2 = Map.fromList [(pP, 1), (fA, 1), (fB, 1)]


clause3 = Clause 
    [ Pos (R ("P", [Fn ("a", [])]))
    , Pos (R ("P", [Fn ("f", [Fn ("a", [])])]))
    ]
expectedFV3 = Map.fromList [(pP, 2), (fF, 1), (fA, 2)]


clause4 = Clause 
    [ Pos (R ("P", [Fn ("a", [])]))
    , Neg (R ("P", [Fn ("a", [])]))
    ]
expectedFV4 = Map.fromList [(pP, 1), (notPP, 1), (fA, 2)]


clause5 = Clause [Pos (R ("Q", [Fn ("f", [Fn ("f", [Fn ("f", [Fn ("b", [])])])])]))]
expectedFV5 = Map.fromList [(pQ, 1), (fF, 3), (fB, 1)]


testFV1 = getFeatureVector clause1 == expectedFV1
testFV2 = getFeatureVector clause2 == expectedFV2
testFV3 = getFeatureVector clause3 == expectedFV3
testFV4 = getFeatureVector clause4 == expectedFV4
testFV5 = getFeatureVector clause5 == expectedFV5

runGetFeatureVectorTests = concat
    [
        "\n\n Running Get Feature Vector Tests", 
        "\n Test 1: " ++ show testFV1,
        "\n Test 2: " ++ show testFV2,
        "\n Test 3: " ++ show testFV3,
        "\n Test 4: " ++ show testFV4,
        "\n Test 5: " ++ show testFV5
    ]