{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Socrates where 
import FOL ( Literal(Pos, Neg), Predicate(R), Term(Fn, Var), Clause (..) )
import GivenClauseLoop.Helpers (createAxioms)

clause1 = [Neg(R("Man", [Var "X"])), Pos(R("Mortal", [Var "X"]))]
clause2 = [Pos(R("Man", [Fn("Socrates", [])]))]
negatedConjecture = [Pos(R("Mortal", [Fn("Socrates", [])]))]

problem = [clause1, clause2, negatedConjecture]

socratesAxioms = createAxioms (map Clause problem)
