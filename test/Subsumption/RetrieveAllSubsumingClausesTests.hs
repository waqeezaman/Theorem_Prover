{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.RetrieveAllSubsumingClausesTests (runRetrieveAllSubsumingClausesTests) where
import Subsumption.SubsumptionFilter
    ( getFeatureVector,
      retrieveAllSubsumingClauses,
      ClauseTrie(ClauseTrieNode),
      getSymbolOrder )
import qualified Data.Map as Map
import FOL ( Clause(..), Literal(..), Predicate(..), Term(..) )
import qualified Data.Set as Set

clause1 = Clause [Pos (R ("P", []))]
clause2 = Clause [Neg (R ("P", []))]
clause3 = Clause [Pos (R ("Q", [Fn ("A", [])]))]
clause4 = Clause [Pos (R ("Q", [Fn ("F", [Fn ("B", [])])]))]
clause5 = Clause [Neg (R ("P", [])), Pos (R ("Q", [Fn ("A", [])]))] 
clause6 = Clause [Pos (R ("Q", [Fn ("F", [Fn ("B", [])])])), Pos (R ("P", []))]



clause1FV = getFeatureVector clause1
clause2FV = getFeatureVector clause2
clause3FV = getFeatureVector clause3
clause4FV = getFeatureVector clause4
clause5FV = getFeatureVector clause5
clause6FV = getFeatureVector clause6

trie = ClauseTrieNode []
    (Map.fromList [(0, ClauseTrieNode []
                        (Map.fromList
                        [
                            (0, ClauseTrieNode []
                                (Map.fromList
                                [
                                    (0, ClauseTrieNode []
                                        (Map.fromList
                                            [
                                                (0, ClauseTrieNode []
                                                    (Map.fromList
                                                    [
                                                        (0, ClauseTrieNode []
                                                            (Map.fromList
                                                            [
                                                                (1, ClauseTrieNode [clause2] Map.empty)
                                                            ])
                                                        )
                                                    ])
                                                ),
                                                (1, ClauseTrieNode []
                                                    (Map.fromList
                                                    [
                                                        (0, ClauseTrieNode []
                                                            (Map.fromList
                                                            [
                                                                (0, ClauseTrieNode [clause1] Map.empty)
                                                            ])
                                                        )
                                                    ])
                                                )
                                            ])
                                    )
                                ])
                            ),
                            (1, ClauseTrieNode []
                                (Map.fromList
                                [
                                    (1, ClauseTrieNode []
                                        (Map.fromList
                                            [
                                                (0, ClauseTrieNode []
                                                    (Map.fromList
                                                    [
                                                        (1, ClauseTrieNode []
                                                            (Map.fromList
                                                            [
                                                                (0, ClauseTrieNode [clause4] Map.empty)
                                                            ])
                                                        )
                                                    ])
                                                ),
                                                (1, ClauseTrieNode []
                                                    (Map.fromList
                                                    [
                                                        (1, ClauseTrieNode []
                                                            (Map.fromList
                                                            [
                                                                (0, ClauseTrieNode [clause6] Map.empty)
                                                            ])
                                                        )
                                                    ])
                                                )
                                            ])
                                    )
                                ])
                            )
                        ])
                    ),
                    (1, ClauseTrieNode []

                        (Map.fromList
                        [
                            (0, ClauseTrieNode []
                                (Map.fromList
                                [
                                    (0, ClauseTrieNode []
                                        (Map.fromList
                                            [
                                                (0, ClauseTrieNode []
                                                    (Map.fromList
                                                    [
                                                        (1, ClauseTrieNode []
                                                            (Map.fromList
                                                            [
                                                                (0, ClauseTrieNode [clause3] Map.empty),
                                                                (1, ClauseTrieNode [clause5] Map.empty)
                                                            ])
                                                        )
                                                    ])
                                                )
                                            ])
                                    )
                                ])
                            )
                        ])
                    )

                    ]
                )

symbolOrdering = getSymbolOrder [clause1, clause2, clause3, clause4, clause5, clause6]

retrieval1 = retrieveAllSubsumingClauses symbolOrdering clause1FV trie
expected1 = [clause1]

retrieval2 = retrieveAllSubsumingClauses symbolOrdering clause2FV trie
expected2 = [clause2]

retrieval3 = retrieveAllSubsumingClauses symbolOrdering clause3FV trie
expected3 = [clause3]

retrieval4 = retrieveAllSubsumingClauses symbolOrdering clause4FV trie
expected4 = [clause4]

retrieval5 = retrieveAllSubsumingClauses symbolOrdering clause5FV trie
expected5 = [clause2, clause3, clause5]

retrieval6 = retrieveAllSubsumingClauses symbolOrdering clause6FV trie
expected6 = [clause1, clause4, clause6]

retrieval7 = retrieveAllSubsumingClauses symbolOrdering Map.empty trie
expected7 = []


test1 = retrieval1 == expected1
test2 = retrieval2 == expected2
test3 = retrieval3 == expected3
test4 = retrieval4 == expected4 
test5 = Set.fromList retrieval5 == Set.fromList expected5 
test6 = Set.fromList retrieval6 == Set.fromList expected6
test7 = retrieval7 == expected7



runRetrieveAllSubsumingClausesTests = concat
    [ "\n\n Running Retrieve All Subsuming Clauses tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5,
        "\n Test 6: " ++ show test6,
        "\n Test 7: " ++ show test7
    ]
