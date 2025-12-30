{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use ++" #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Unification.SubInListTests (runSubInListTests) where

import FOL
import Unification


list1 = [(Var "X", Fn ("F", []))]
subbedList1 = [(Fn ("G", []), Fn ("F", []))]

list2 = [(Var "Y", Fn ("F", [Var "Y"]))]
subbedList2 = [(Var "X", Fn ("F", [Var "X"]))]

list3 = 
    [
        (Var "Y", Fn ("F", [Var "Y", Var "Y"])),
        (Fn ("F", [Var "Y", Var "Y"]), Var "Y")
    ]

subbedList3 = 
    [
        (Fn("G", []), Fn ("F", [Fn("G", []), Fn("G", [])])),
        (Fn ("F", [Fn("G", []), Fn("G", [])]), Fn("G", []))

    ]

list4 = []
subbedList4 = []

list5 = 
    [
        (Var "Y", Fn ("F", [Var "X", Var "Y"])),
        (Fn ("F", [Var "Y", Var "X"]), Var "X")
    ]

subbedList5 = 
    [
        (Fn("G", [Var "Z"]), Fn ("F", [Var "X", Fn("G", [Var "Z"])])),
        (Fn ("F", [Fn("G", [Var "Z"]), Var "X"]), Var "X")
    ]

list6 = 
    [
        (
            Var "Y",
            Fn ("F", [Fn("H", [Var "Y"]), Var "Y"])),
        (Fn ("F", [Var "Y", Fn("H", [Var "Y"])]), Var "X")
    ]
subbedList6 = 
    [
        (
            Fn("G", [Var "Z"]),
            Fn ("F", 
                [
                    Fn("H", [Fn("G", [Var "Z"])]),
                    Fn("G", [Var "Z"])
                ])
        ),
        (
            Fn ("F", 
                [
                    Fn("G", [Var "Z"]),
                    Fn("H", [Fn("G", [Var "Z"])])
                ]
            ),
            Var "X")
    ]

test1 = subInList (Var "X") (Fn ("G", [])) list1 == subbedList1
test2 = subInList (Var "Y") (Var "X") list2 == subbedList2
test3 = subInList (Var "Y") (Fn("G", [])) list3 == subbedList3
test4 = subInList (Var "Y") (Fn("G", [])) list4 == subbedList4
test5 = subInList (Var "Y") (Fn("G", [Var "Z"])) list5 == subbedList5
test6 = subInList (Var "Y") (Fn("G", [Var "Z"])) list6 == subbedList6



runSubInListTests = concat
    [
        "\n\n Running Sub In List Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3,
        "\n Test 4: " ++ show test4,
        "\n Test 5: " ++ show test5,
        "\n Test 6: " ++ show test6
    ]