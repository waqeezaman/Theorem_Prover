import FOL
 
functions:: Int -> String -> [Int] -> Int

functions n "0"  []  = 0
functions n "1"  []  = mod 1 n
functions n "+"  [x,y] = mod (x+y) n
functions n "*"  [x,y] = mod (x*y) n
functions _ _ _ = error "Undefined Function"



predicates :: String -> [Int] -> Bool
predicates "=" [x,y] = x==y
predicates _ _ = error "Undefined Predicate"

n = 4

sigN n = ( [0..n-1], functions n, predicates   )


sig :: ([Int], String -> [Int] -> Int, String -> [Int] -> Bool)
sig = sigN n 



formula = 
    Forall "X" 
            (Or
                (Atom  (R ("=",  [ Fn ("0",  []) , Var "X"  ] ) ) )
                (Atom  (R ("=",  [ Fn ("1",  [])  , Var "X" ] ) ) )
        
            ) 


formula2 = Forall "X"
                (Imp
                    (Not  
                        (Atom (R ("=",  [ Fn ("0",  []) , Var "X"  ] )) )
                    )
                    (Exists "Y"
                        (Atom  (R ("=",  [ Fn ("1",  [])  , Fn ("*" , [Var "X", Var "Y"])    ] ) ) )
                    )
                )

valuation _ = 0


result = holds sig valuation formula2

main = print result 

