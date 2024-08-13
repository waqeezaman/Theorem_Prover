import FOL

preds :: Eq a => String -> [a] -> Bool
preds "=" [x,y] = x==y

functions :: String -> [Bool] -> Bool
functions "0" [] = False
functions "1" [] = True
functions "+" [x,y] = not x==y
functions "*" [x,y] = x && y


sig :: Eq d => ([Bool], String -> [Bool] -> Bool,   String -> [d] -> Bool)
sig = ([False, True], functions, preds)

formula = Forall(Var "X") 
    (And
        
        (Atom(R ( "=",  [ Var "X" , Fn ("+" ,[Var "X",Var "Y"] )  ])  ) ) 
        
        (Not 
            ( Atom(R( "=" , [ Var "X" , Fn ("+", [Var "X", Var "Y"] )  ])  ) )
        )
    ) 


valuation "Y" = False

result = holds sig valuation formula


main = print result