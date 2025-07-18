module BinaryTests where


import FOL
import FOL (Formula(Forall))



preds :: Eq a => String -> [a] -> Bool
preds "=" [x,y] = x==y

functions :: String -> [Bool] -> Bool
functions "0" [] = False
functions "1" [] = True
functions "+" [x,y] = not x==y
functions "*" [x,y] = x && y


sig :: Eq d => ([Bool], String -> [Bool] -> Bool,   String -> [d] -> Bool)
sig = ([False, True], functions, preds)

valuation :: String -> Bool
valuation "Y" = False


-- test to check that  P AND NOT P is FALSE
formula1 :: Formula
formula1 = Forall "X" 
    (And
        
        (Atom(R ( "=",  [ Var "X" , Fn ("+" ,[Var "X",Var "Y"] )  ])  ) ) 
        
        (Not 
            ( Atom(R( "=" , [ Var "X" , Fn ("+", [Var "X", Var "Y"] )  ])  ) )
        )
    ) 


-- test to check that P = 0 OR P = 1 is TRUE
formula2 :: Formula 
formula2 = Forall "X"
            (
                Atom( R("=", [Var "X", Fn ("0", [])] ) )
                `Or`
                Atom( R("=", [Var "X", Fn ("1", [])] ) )
            )




test1 :: Bool
test1 = holds sig valuation formula1 == False

test2 :: Bool 
test2 = holds sig valuation formula2 == True






runBinaryTests =    "\n Running Binary Tests \n " ++ 
                    "\n Test 1:" ++ show test1 ++ 
                    "\n Test 2:" ++ show test2 ++ 
                    "\n"