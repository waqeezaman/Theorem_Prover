{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use null" #-}
module Factoring.SamePolarityPairsTests where
import FOL ( Predicate(..), Literal(..) )
import Factoring (samePolarityPairs)
import Utils (uniquePairs)
import qualified Data.Set as Set


literal1 = Neg (R ("P", []))
literal2 = Pos (R ("P", []))
literal3 = Neg (R ("Q", []))
literal4 = Pos (R ("R", []))
literal5 = Neg (R ("P", []))


pairs = uniquePairs [literal1, literal2, literal3, literal4, literal5]


test1 = samePolarityPairs [] == []
test2 = Set.fromList (samePolarityPairs pairs) == Set.fromList [(literal1, literal3), (literal2, literal4), (literal1, literal5), (literal3, literal5)]


runSamePolarityPairsTests = concat
    [
        "\n\n Running Same Polarity Pairs Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2
    ]