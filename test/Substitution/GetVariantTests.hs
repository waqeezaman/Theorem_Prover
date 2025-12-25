{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Substitution.GetVariantTests where 
import Substitution (getVariant)

test1 = getVariant "X" ["Y", "Z"] == "X"
test2 = getVariant "X" ["X", "Y"] == "X#"
test3 = getVariant "X" ["X", "X#"] == "X##"

runGetVariantTests = concat   
    [
        "\n\n Running Get Variant Tests",
        "\n Test 1: " ++ show test1,
        "\n Test 2: " ++ show test2,
        "\n Test 3: " ++ show test3
    ]