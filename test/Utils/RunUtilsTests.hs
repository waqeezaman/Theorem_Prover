{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Utils.RunUtilsTests where 
import Utils.DisjunctionToLiteralListTests (runDisjunctionToLiteralListTests)
import Utils.CNFToClausalFormTests (runCNFToClausalFormTests)

runUtilsTests = concat 
    [
        "\n\n\n Running Utils Tests", 
        runDisjunctionToLiteralListTests,
        runCNFToClausalFormTests
    ]