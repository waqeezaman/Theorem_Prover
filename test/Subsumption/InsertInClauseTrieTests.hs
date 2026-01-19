{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.InsertInClauseTrieTests where
import Subsumption.SubsumptionFilter (ClauseTrie(ClauseTrieNode), insertInClauseTrie, getSymbolOrder, getFeatureVector, emptyClauseTrie)
import qualified Data.Map as Map
import FOL ( Literal(..), Clause(..), Predicate(..), Term(..) )

clause1 = Clause [Pos (R ("P", []))]
clause2 = Clause [Neg (R ("P", []))]
clause3 = Clause [Pos (R ("Q", [Fn ("A", [])]))]
clause4 = Clause [Pos (R ("Q", [Fn ("F", [Fn ("B", [])])]))]

clause1FV = getFeatureVector clause1
clause2FV = getFeatureVector clause2
clause3FV = getFeatureVector clause3
clause4FV = getFeatureVector clause4

baseTrie = ClauseTrieNode []
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
                                                                (0, emptyClauseTrie)
                                                            ])
                                                        )
                                                    ])
                                                )
                                            ])
                                    )
                                ])
                            )
                        ])
                    )]
                )

step1ExpectedTrie = ClauseTrieNode []
    (Map.fromList [(0, ClauseTrieNode []
            
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
                            )
                        ])
                    )]
                )

step2ExpectedTrie = ClauseTrieNode []
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
                            )
                        ])
                    )]
                )

step3ExpectedTrie = ClauseTrieNode []
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
                                                                (0, ClauseTrieNode [clause3] Map.empty)
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

step4ExpectedTrie = ClauseTrieNode []
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
                                                                (0, ClauseTrieNode [clause3] Map.empty)
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

symbolOrdering = getSymbolOrder [clause1, clause2, clause3, clause4]

step1 = insertInClauseTrie symbolOrdering clause1 clause1FV emptyClauseTrie
step2 = insertInClauseTrie symbolOrdering clause2 clause2FV step1
step3 = insertInClauseTrie symbolOrdering clause3 clause3FV step2
step4 = insertInClauseTrie symbolOrdering clause4 clause4FV step3

test1 = step1 == step1ExpectedTrie
test2 = step2 == step2ExpectedTrie
test3 = step3 == step3ExpectedTrie
test4 = step4 == step4ExpectedTrie

runInsertInClauseTrieTests = concat
    ["\n\n Running insert in clause trie tests",
        concatMap (++ "  ") symbolOrdering,
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4
    ]