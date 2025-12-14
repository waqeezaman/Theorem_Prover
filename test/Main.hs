module Main (main) where

import SubstitutionTests
import BinaryTests
import ModTests (runModTests)
import SimplificationTests (runSimplificationTests)
import PrenexTests (runPrenexTests)

testOutputs =   runBinaryTests ++
                runModTests ++
                runSubstitutionTests ++ 
                runSimplificationTests ++ 
                runPrenexTests

main :: IO ()
main = putStrLn testOutputs
