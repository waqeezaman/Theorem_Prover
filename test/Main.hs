module Main (main) where

import SubstitutionTests
import BinaryTests (runBinaryTests)
import ModTests (runModTests)
import SimplificationTests (runSimplificationTests)

testOutputs =   runBinaryTests ++
                runModTests ++
                runSubstitutionTests ++ 
                runSimplificationTests

main :: IO ()
main = putStrLn (testOutputs)
