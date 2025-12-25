{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use ++" #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Substitution.RunSubstitutionTests where
import Substitution.TermSubstitutionTests (runTermSubstitutionTests)
import Substitution.FormulaSubstitutionTests (runFormulaSubstitutionTests)
import Substitution.GetVariantTests (runGetVariantTests)


runSubstitutionTests  = concat 
    [
        "\n\n\n Running Substitution Tests: ",
        runGetVariantTests, 
        runTermSubstitutionTests,
        runFormulaSubstitutionTests
    ]