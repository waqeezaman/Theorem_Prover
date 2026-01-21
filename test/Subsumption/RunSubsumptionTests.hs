{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Subsumption.RunSubsumptionTests (runSubsumptionTests) where
import Subsumption.ExtractSymbolsFromTermTests (runExtractSymbolsFromTermTests)
import Subsumption.ExtractSymbolsFromLiteralTests (runExtractSymbolsFromLiteralTests)
import Subsumption.ExtractSymbolsFromClauseTests (runExtractSymbolsFromClauseTests)
import Subsumption.GetFeatureVectorTests (runGetFeatureVectorTests)
import Subsumption.GetSymbolOrderTests (runGetSymbolOrderTests)
import Subsumption.InsertInClauseTrieTests (runInsertInClauseTrieTests)
import Subsumption.RetrieveAllPossiblySubsumingClausesTests (runRetrieveAllPossiblySubsumingClausesTests)
import Subsumption.GetVarsInClauseTests (runGetVarsInClauseTests)
import Subsumption.GroundClauseTests (runGroundClauseTests)
import Subsumption.MatchTermTests (runMatchTermTests)
import Subsumption.MatchTermsTests (runMatchTermsTests)
import Subsumption.MatchPredicatesTests (runMatchPredicatesTests)
import Subsumption.MatchLiteralsTests (runMatchLiteralsTests)
import Subsumption.CanMatchTests (runCanMatchTests)
import Subsumption.IsSubsumedByTests (runIsSubsumedByTests)

runSubsumptionTests = concat 
    [
        "\n\n\n Running Subsumption Tests:",
        runExtractSymbolsFromTermTests,
        runExtractSymbolsFromLiteralTests,
        runExtractSymbolsFromClauseTests, 
        runGetFeatureVectorTests,
        runGetSymbolOrderTests,
        runInsertInClauseTrieTests,
        runRetrieveAllPossiblySubsumingClausesTests, 
        runGetVarsInClauseTests,
        runGroundClauseTests,
        runMatchTermTests,
        runMatchTermsTests,
        runMatchPredicatesTests,
        runMatchLiteralsTests,
        runCanMatchTests,
        runIsSubsumedByTests
    ]