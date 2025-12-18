module CNF where

import FOL ( Formula(And, Or) )

-- Multiply Out function 
-- Expands formulas by distributing variables 
-- This is the main point where the conversion to CNF occurs 
-- Uses the identity   P ∨ (Q ∧ R) ≡ (P ∨ Q) ∧ (P ∨ R)
multiplyOut :: Formula -> Formula 
multiplyOut formula = case formula of 
    p `Or` (q `And` r) -> (p `Or` q) `And` (p `Or` r)
    (q `And` r) `Or` p -> (q `Or` p) `And` (r `Or` p)
    _ -> formula

-- Recursively steps down the formula 
-- Applying the multiply out function to each subformula 
toCNFRecurse :: Formula -> Formula 
toCNFRecurse formula = case formula of 
    p `Or` q -> multiplyOut (toCNFRecurse p `Or` toCNFRecurse q) 
    p `And` q -> multiplyOut (toCNFRecurse p `And` toCNFRecurse q) 
    _ ->  formula


-- Converts a formula in Disjunctive Normal Form 
-- to Conjunctive Normal Form
toCNF :: Formula -> Formula 
toCNF formula =
    let newFormula = toCNFRecurse formula in
    if formula == newFormula then formula else toCNF newFormula
