{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Factoring.RunFactoringTests where
import Factoring.SamePolarityPairsTests (runSamePolarityPairsTests)
import Factoring.FactoriseTests (runFactoriseTests)
import Factoring.ApplyFactorisationTests (runApplyFactoringTests)


runFactoringTests = concat
    [
        "\n\n\n Running Factoring Tests",
        runSamePolarityPairsTests,
        runApplyFactoringTests,
        runFactoriseTests
    ]