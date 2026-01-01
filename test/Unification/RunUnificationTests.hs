{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Unification.RunUnificationTests where 

import Unification.FormulaContainsVarTests (runFormulaContainsVarTests)
import Unification.TermContainsVarTests (runTermContainsVarTests)
import Unification.StandardiseApartTests (runStandardiseApartTests)
import Unification.SubInListTests(runSubInListTests)
import Unification.TermUnificationTests(runTermUnificationTests)
import Unification.PredicateUnificationTests(runPredicateUnificationTests)
import Unification.UnifyTests (runUnifyTests)
import Unification.ApplySubToTermsTests (runApplySubToTermsTests)
import Unification.ApplySubToLiteralTests (runApplySubToLiteralTests)
import Unification.ApplySubToClauseTests (runApplySubToClauseTests)
import Unification.VariablesInClauseTests (runVariablesInClauseTests)
import Unification.CreateStandardisingSubTests (runCreateStandardisingSubTests)
import Unification.StandardiseApartClauseTests (runStandardiseApartClauseTests)

runUnificationTests = concat 
    [
        "\n\n\n Running Unification Tests",
        runFormulaContainsVarTests,
        runTermContainsVarTests,
        runStandardiseApartTests,
        runSubInListTests,
        runTermUnificationTests,
        runPredicateUnificationTests,
        runUnifyTests,
        runApplySubToTermsTests,
        runApplySubToLiteralTests,
        runApplySubToClauseTests,
        runVariablesInClauseTests,
        runCreateStandardisingSubTests,
        runStandardiseApartClauseTests
    ]