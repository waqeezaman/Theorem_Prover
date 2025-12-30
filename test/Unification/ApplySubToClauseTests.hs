{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use null" #-}
module Unification.ApplySubToClauseTests (runApplySubToClauseTests) where 
import qualified Data.Map as Map
import FOL
import Unification (applySubToClause)


t1 = Var "X"
t2 = Var "Y"
t3 = Fn ("F", [t1, t2])
t4 = Fn ("G", [Fn ("F", [t3, t1])])
t5 = Var "Z"


literal1 = Pos (R ("P", [t1]))

literal2 = Neg (R ("Q", [t2]))

literal3 = Pos (R ("R", [t3]))

literal4 = Neg (R ("S", [t4]))

literal5 = Neg (R ("T", [t1, t2, t3, t4]))
literal6 = Pos(R("U", [t1, t2, t5]))


clause1 = []
clause2 = [literal1]
clause3 = [literal1, literal2]
clause4 = [literal1, literal2, literal3]
clause5 = [literal1, literal2, literal3, literal4, literal5]
clause6 = [literal6]

sub = Map.fromList [(Var "X", Fn ("A", [])), (Var "Y", Fn ("B", []))]


subbedL1 =  Pos (R ("P", [Fn ("A", [])]))

subbedL2 =  Neg (R ("Q", [Fn ("B", [])]))
subbedL3 =  Pos (R ("R", [Fn ("F", [ Fn ("A", []), Fn ("B", [])])]))
subbedL4 = Neg (R("S", [
                            Fn ("G", [Fn ("F",
                                            [
                                                Fn ("F", [ Fn ("A", []), Fn ("B", [])]),
                                                Fn ("A", [])
                                            ]
                                        )
                                    ]
                                )
                        ]
                    ))

subbedL5 = Neg(R("T", [
        Fn ("A", []),
        Fn ("B", []),
        Fn ("F", [ Fn ("A", []), Fn ("B", [])]),
        Fn ("G", [Fn ("F",
                                            [
                                                Fn ("F", [ Fn ("A", []), Fn ("B", [])]),
                                                Fn ("A", [])
                                            ]
                                        )
                                    ]
                                )
    ]))

subbedL6 = Pos(R("U", [Fn("A", []), Fn("B", []), Var "Z"]))

test1 = applySubToClause sub clause1 == []
test2 = applySubToClause sub clause2 == [subbedL1]
test3 = applySubToClause sub clause3 == [subbedL1, subbedL2]
test4 = applySubToClause sub clause4 == [subbedL1, subbedL2, subbedL3]
test5 = applySubToClause sub clause5 == [subbedL1, subbedL2, subbedL3, subbedL4, subbedL5]
test6 = applySubToClause sub clause6 == [subbedL6]

runApplySubToClauseTests = concat
    [
        "\n\n Running Apply Sub To Clause Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5,
        "\n Test 6: " ++ show test6 
    ]