module Main (main) where

import SubstitutionTests
import BinaryTests
import ModTests (runModTests)
import SimplificationTests (runSimplificationTests)
import PrenexTests (runPrenexTests)
import SkolemTests
import CNFTests

testOutputs =   runBinaryTests ++
                runModTests ++
                runSubstitutionTests ++ 
                runSimplificationTests ++ 
                runPrenexTests ++ 
                runSkolemTests ++ 
                runCNFTests

main :: IO ()
main = putStrLn testOutputs
