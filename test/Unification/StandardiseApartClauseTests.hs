{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Unification.StandardiseApartClauseTests (runStandardiseApartClauseTests) where

import Unification
import FOL



clause1A = [Pos(R ("P", [Var "X", Var "Y"]))]
clause1B = [Pos(R ("P", [Var "X", Var "Y"]))]
expectedClause1B = [Pos (R ("P", [Var "X#", Var "Y#"]))]

clause2A = [Neg(R ("P", [Var "X", Var "Y"]))]
clause2B = [Pos(R ("P", [Var "X", Var "Y"]))]
expectedClause2B = [Pos(R ("P", [Var "X#", Var "Y#"]))]

clause3A = [Pos(R ("P", [Var "X", Var "X"])), Pos (R ("P", [Var "Y#", Var "Y"]))]
clause3B = [Neg(R ("P", [Var "X", Var "Y#"]))]
expectedClause3B = [Neg (R ("P", [Var "X#", Var "Y##"]))]

clause4A = [Pos (R ("P", [Var "Y#", Var "X"])), Pos (R ("P", [Var "Y##", Var "Y###"]))]
clause4B = [Neg (R ("Q", [Var "X", Var "Y###", Var "X#"]))]
expectedClause4B = [Neg (R ("Q", [Var "X##", Var "Y####", Var "X#"]))]

clause5A = [Pos (R ("P", [Var "X", Var "Y"])), Pos (R ("P", [Var "Z", Var "W"]))]
clause5B = [Pos (R ("P", [Var "X", Var "Y"])), Pos (R ("P", [Var "Z", Var "W"]))]
expectedClause5B = [Pos (R ("P", [Var "X#", Var "Y#"])), Pos (R ("P", [Var "Z#", Var "W#"]))]

test1 = standardiseApartClause clause1A clause1B == expectedClause1B
test2 = standardiseApartClause clause2A clause2B == expectedClause2B
test3 = standardiseApartClause clause3A clause3B == expectedClause3B
test4 = standardiseApartClause clause4A clause4B == expectedClause4B
test5 = standardiseApartClause clause5A clause5B == expectedClause5B


runStandardiseApartClauseTests = concat
    [
        "\n\n Running Standardise Apart Clause Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5
    ]