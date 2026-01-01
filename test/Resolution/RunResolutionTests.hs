{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Resolution.RunResolutionTests (runResolutionTests) where
import Resolution.OpposingPolarityPairsTests (runOpposingPolarityPairsTests)
import Resolution.ApplyResolutionTests (runApplyResolutionTests)
import Resolution.ResolveTests (runResolveTests)



runResolutionTests = concat 
    [
        "\n\n\n Running Resolution Tests",
        runOpposingPolarityPairsTests,
        runApplyResolutionTests,
        runResolveTests
    ]
