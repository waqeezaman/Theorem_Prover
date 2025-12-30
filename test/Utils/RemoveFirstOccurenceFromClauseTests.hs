{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Utils.RemoveFirstOccurenceFromClauseTests (runRemoveFirstOccurenceFromClauseTests) where 
import FOL
import Utils (removeFirstOccurenceFromClause)

    
lit1 = Pos(R("P", []))
lit2 = Pos(R("Q", []))
lit3 = Pos(R("R", []))
lit4 = Pos(R("S", []))

clause1 = [lit1, lit2, lit3, lit4]
clause2 = []
clause3 = [lit1, lit1, lit2]

test1 = removeFirstOccurenceFromClause clause1 lit1 == [lit2, lit3, lit4]
test2 = removeFirstOccurenceFromClause clause1 lit2 == [lit1, lit3, lit4]
test3 = removeFirstOccurenceFromClause clause1 lit3 == [lit1, lit2, lit4]
test4 = removeFirstOccurenceFromClause clause1 lit4 == [lit1, lit2, lit3]

test5 = removeFirstOccurenceFromClause clause2 lit1 == clause2

test6 = removeFirstOccurenceFromClause clause3 lit1 == [lit1, lit2]

runRemoveFirstOccurenceFromClauseTests = concat 
    [
        "\n\n Running Remove First Occurence From Clause Tests",
        "\n Test 1: " ++ show test1, 
        "\n Test 2: " ++ show test2, 
        "\n Test 3: " ++ show test3, 
        "\n Test 4: " ++ show test4, 
        "\n Test 5: " ++ show test5,
        "\n Test 6: " ++ show test6 
    ]