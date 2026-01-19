{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.RunSubsumptionTests (runSubsumptionTests) where
import Subsumption.ExtractSymbolsFromTermTests (runExtractSymbolsFromTermTests)
import Subsumption.ExtractSymbolsFromLiteralTests (runExtractSymbolsFromLiteralTests)
import Subsumption.ExtractSymbolsFromClauseTests (runExtractSymbolsFromClauseTests)
import Subsumption.GetFeatureVectorTests (runGetFeatureVectorTests)
import Subsumption.GetSymbolOrderTests (runGetSymbolOrderTests)
import Subsumption.InsertInClauseTrieTests (runInsertInClauseTrieTests)
import Subsumption.RetrieveAllSubsumingClausesTests (runRetrieveAllSubsumingClausesTests)

runSubsumptionTests = concat 
    [
        "\n\n\n Running Subsumption Tests:",
        runExtractSymbolsFromTermTests,
        runExtractSymbolsFromLiteralTests,
        runExtractSymbolsFromClauseTests, 
        runGetFeatureVectorTests,
        runGetSymbolOrderTests,
        runInsertInClauseTrieTests,
        runRetrieveAllSubsumingClausesTests
    ]