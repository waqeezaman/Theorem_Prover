module FOL where 
import Data.List (union, delete)

import Data.Set (Set)
import qualified Data.Set as Set


    
data Term = Var String | Fn (String , [Term] ) deriving (Eq,Show)

data Predicate = R (String, [Term])  deriving (Eq, Show)

data Formula = FFalse | FTrue | Atom Predicate | Not Formula 
                | And Formula Formula | Or Formula Formula 
                | Imp Formula Formula | Iff Formula Formula
                | Forall  String Formula | Exists String Formula deriving (Eq,Show)



-- Returns the valuation of a term given a valuation function and a signature

termval :: (a, String -> [b] -> b, c) -> (String -> b) -> Term -> b
termval (domain, functions, predicates ) v (Var x) = v  x

termval (domain, functions, predicates) v (Fn (func ,terms)) = 
    functions func ( map (termval (domain, functions,predicates) v) terms) 



-- Determines whether a formula holds given a valuation function and a signature 

holds :: Foldable t => (t b, String -> [b] -> b, String -> [b] -> Bool) -> (String -> b) -> Formula -> Bool
holds (domain, functions, predicates) v FFalse = False
holds (domain, functions, predicates) v FTrue = True
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






