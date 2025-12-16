module Main (main) where

import SubstitutionTests
import BinaryTests
import ModTests (runModTests)
import SimplificationTests (runSimplificationTests)
import PrenexTests (runPrenexTests)
import SkolemTests

testOutputs =   runBinaryTests ++
                runModTests ++
                runSubstitutionTests ++ 
                runSimplificationTests ++ 
                runPrenexTests ++ 
                runSkolemTests

main :: IO ()
main = putStrLn testOutputs
