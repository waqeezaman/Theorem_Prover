{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant ==" #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module BinaryTests where

import FOL
    ( Formula(Or, And, Not, Forall, Atom),
      Predicate(R),
      Term(Fn, Var),
      holds,
      Formula(Forall) )

preds "=" [x,y] = x==y
preds _ _ = error "Undefined Predicate"

functions "0" [] = False
functions "1" [] = True
functions "+" [x,y] = not x==y
functions "*" [x,y] = x && y
functions _ _ = error "Undefined Function"

sig = ([False, True], functions, preds)

valuation :: String -> Bool
valuation "Y" = False
valuation _ = error "Undefined Input for Valuation"


-- test to check that  P AND NOT P is FALSE
formula1 = Forall "X"
    (And

        (Atom (R ( "=",  [ Var "X" , Fn ("+" ,[Var "X",Var "Y"] )  ])  ) )

        (Not
            ( Atom (R ( "=" , [ Var "X" , Fn ("+", [Var "X", Var "Y"] )  ])  ) )
        )
    )

-- test to check that P = 0 OR P = 1 is TRUE
formula2 = Forall "X"
            (
                Atom ( R ("=", [Var "X", Fn ("0", [])] ) )
                `Or`
                Atom ( R ("=", [Var "X", Fn ("1", [])] ) )
            )

test1 = holds sig valuation formula1 == False

test2 = holds sig valuation formula2 == True

runBinaryTests = concat 
    [
        "\n\n Running Binary Tests",
        "\n Test 1:" ++ show test1,
        "\n Test 2:" ++ show test2
    ]   