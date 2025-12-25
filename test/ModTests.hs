{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant ==" #-}
{-# HLINT ignore "Use ++" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module ModTests where 

import FOL
    ( Formula(Atom, Forall, Or), Predicate(R), Term(Var, Fn), holds )
 
functions:: Int -> String -> [Int] -> Int

functions _ "0"  []  = 0
functions n "1"  []  = mod 1 n
functions n "+"  [x,y] = mod (x+y) n
functions n "*"  [x,y] = mod (x*y) n
functions _ _ _ = error "Undefined Function"

predicates :: String -> [Int] -> Bool
predicates "=" [x,y] = x==y
predicates _ _ = error "Undefined Predicate"

n = 3

sigN n = ( [0..n-1], functions n, predicates   )

sig :: ([Int], String -> [Int] -> Int, String -> [Int] -> Bool)
sig = sigN n 

formula1 = 
    Forall "X" 
            (Or
                (Atom  (R ("=",  [ Fn ("0",  []) , Var "X"  ] ) ) )
                (Atom  (R ("=",  [ Fn ("1",  [])  , Var "X" ] ) ) )
        
            ) 

valuation _ = 0


test1 = holds sig valuation formula1 == False

runModTests = concat 
    [
        "\n\n Running Mod Tests",
        "\n Test 1: " ++ show test1
    ]