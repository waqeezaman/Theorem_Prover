module FOL (
    Term(..),
    Predicate(..),
    Formula(..), 
    prettyPrintFormula,
    termval,
    holds,
    makeForall, 
    makeExists, 
    makeAnd,
    makeOr
    ) where

data Term = Var String | Fn (String , [Term] ) deriving (Eq, Ord)

newtype Predicate = R (String, [Term])  deriving (Eq)

data Formula = FFalse | FTrue | Atom Predicate | Not Formula
                | And Formula Formula | Or Formula Formula
                | Imp Formula Formula | Iff Formula Formula
                | Forall  String Formula | Exists String Formula deriving (Eq)

instance Show Term where
    show :: Term -> String
    show (Var x) = x
    show (Fn(x, terms)) = x ++ show terms

instance Show Predicate where
    show :: Predicate -> String
    show (R(pred, terms)) = pred++ show terms

instance Show Formula where
    show FFalse = "⊥"
    show FTrue = "⊤"
    show (Atom p) = show p
    show (Not formula) = "¬( " ++ show formula ++ ")"
    show (And p q) = "(" ++ show p ++ " & " ++ show q  ++ ")"
    show (Or p q) = "(" ++ show p ++ " | " ++ show q ++ ")"
    show (Imp p q) = "(" ++ show p ++ " → " ++ show q ++ ")"
    show (Iff p q) = "(" ++ show p ++ " ↔ " ++ show q ++ ")"
    show (Forall x formula) = "(∀" ++ x ++ ". " ++  show formula ++ ")"
    show (Exists x formula) = "(∃" ++ x ++ ". " ++  show formula ++ ")"


prettyPrintFormula :: Formula -> String
prettyPrintFormula formula = prettyPrintFormula' formula 0 

prettyPrintFormula' :: Formula -> Int -> String

prettyPrintFormula' FFalse _ = show FFalse
prettyPrintFormula' FTrue _ = show FFalse
prettyPrintFormula' (Atom p)  _ = show p
prettyPrintFormula' (Not p) lvl = "¬("++ prettyPrintFormula' p lvl ++ ")"

prettyPrintFormula' (p `And` q) lvl =    "\n" ++ concat (replicate lvl "    ") ++ "(" ++
                                        prettyPrintFormula' p (lvl+1) ++ 
                                        "\n" ++ concat (replicate lvl "    ") ++ ")" ++
                                        "\n" ++ concat (replicate lvl "    ") ++ "AND" ++
                                        "\n" ++ concat (replicate lvl "    ") ++ "(" ++
                                        prettyPrintFormula' q (lvl+1)  ++  
                                        "\n" ++ concat (replicate lvl "    ") ++ ")"
                                        
prettyPrintFormula' (p `Or` q) lvl =     "\n" ++ concat (replicate lvl "    ") ++ "(" ++
                                        prettyPrintFormula' p (lvl+1) ++ 
                                        "\n" ++ concat (replicate lvl "    ") ++ ")" ++
                                        "\n" ++ concat (replicate lvl "    ") ++ "OR" ++
                                        "\n" ++ concat (replicate lvl "    ") ++ "(" ++
                                        prettyPrintFormula' q (lvl+1)  ++  
                                        "\n" ++ concat (replicate lvl "    ") ++ ")"
                                     

prettyPrintFormula' (p `Imp` q) lvl =    "\n" ++ concat (replicate lvl "    ") ++ "(" ++
                                        prettyPrintFormula' p (lvl+1) ++ 
                                        "\n" ++ concat (replicate lvl "    ") ++ ")" ++
                                        "\n" ++ concat (replicate lvl "    ") ++ "→" ++
                                        "\n" ++ concat (replicate lvl "    ") ++ "(" ++
                                        prettyPrintFormula' q (lvl+1)  ++  
                                        "\n" ++ concat (replicate lvl "    ") ++ ")"
                                     

prettyPrintFormula' (p `Iff` q) lvl =    "\n" ++ concat (replicate lvl "    ") ++ "(" ++
                                        prettyPrintFormula' p (lvl+1) ++ 
                                        "\n" ++ concat (replicate lvl "    ") ++ ")" ++
                                        "\n" ++ concat (replicate lvl "    ") ++ "↔" ++
                                        "\n" ++ concat (replicate lvl "    ") ++ "(" ++
                                        prettyPrintFormula' q (lvl+1)  ++  
                                        "\n" ++ concat (replicate lvl "    ") ++ ")"


prettyPrintFormula' (Forall x p) lvl =  "∀" ++ x ++ "\n" ++ concat (replicate lvl "    ") ++
                                    "(" ++  prettyPrintFormula' p (lvl+1) ++ ")" 
                                  
prettyPrintFormula' (Exists x p) lvl =  "∃" ++ x ++ "\n" ++ concat (replicate lvl "    ") ++
                                    "(" ++  prettyPrintFormula' p (lvl+1) ++ ")" 
                                  

                                     

-- Returns the valuation of a term given a valuation function and a signature

termval :: (a, String -> [b] -> b, c) -> (String -> b) -> Term -> b
termval (_, _, _ ) v (Var x) = v  x

termval (domain, functions, predicates) v (Fn (func ,terms)) =
    functions func ( map (termval (domain, functions,predicates) v) terms)



-- Determines whether a formula holds given a valuation function and a signature 
holds :: Foldable t => (t b, String -> [b] -> b, String -> [b] -> Bool) -> (String -> b) -> Formula -> Bool
holds (_, _, _) _ FFalse = False
holds (_, _, _) _ FTrue = True
holds (domain, functions, predicates) v (Atom(R(pred, terms))) =
    predicates pred (map (termval (domain, functions, predicates) v) terms)

holds (domain, functions, predicates) v (Not p) =
    not (holds (domain, functions, predicates) v p )

holds (domain, functions, predicates) v (And p q) =
    holds (domain, functions, predicates) v p  &&
    holds (domain, functions, predicates) v q

holds (domain, functions, predicates) v (Or p q) =
    holds (domain, functions, predicates) v p  ||
    holds (domain, functions, predicates) v q

holds (domain, functions, predicates) v (Imp p q) =
    not (holds (domain, functions, predicates) v p ) ||
    holds (domain, functions, predicates) v q

holds (domain, functions, predicates) v (Iff p q) =
    holds (domain, functions, predicates) v p ==
    holds (domain, functions, predicates) v q

holds (domain, functions, predicates) v (Forall p q) =
   all  (\a -> let x = a in  holds (domain, functions, predicates )
                            (\x -> if x == p then a else v x) q
        )
   domain

holds (domain, functions, predicates) v (Exists p q) =
   any  (\a -> let x = a in  holds (domain, functions, predicates )
                            (\x -> if x == p then a else v x) q
        )
   domain


makeForall :: [Char] -> Formula -> Formula
makeForall = Forall

makeExists :: [Char] -> Formula -> Formula
makeExists = Exists

makeAnd :: Formula -> Formula -> Formula
makeAnd = And 

makeOr :: Formula -> Formula -> Formula
makeOr = Or