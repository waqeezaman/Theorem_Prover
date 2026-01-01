{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Main (main) where

import Substitution.RunSubstitutionTests (runSubstitutionTests)
import BinaryTests ( runBinaryTests )
import ModTests (runModTests)
import SimplificationTests (runSimplificationTests)
import NNFTests ( runNNFTests )
import PrenexTests (runPrenexTests)
import SkolemTests ( runSkolemTests )
import CNFTests ( runCNFTests )
import Unification.RunUnificationTests (runUnificationTests)
import Utils.RunUtilsTests (runUtilsTests)
import Factoring.RunFactoringTests (runFactoringTests)
import Resolution.RunResolutionTests (runResolutionTests)

testOutputs =   runBinaryTests ++
                runModTests ++
                runSubstitutionTests ++ 
                runSimplificationTests ++
                runNNFTests ++
                runPrenexTests ++ 
                runSkolemTests ++ 
                runCNFTests ++ 
                runUnificationTests ++ 
                runUtilsTests ++ 
                runFactoringTests ++ 
                runResolutionTests

main = putStrLn testOutputs
