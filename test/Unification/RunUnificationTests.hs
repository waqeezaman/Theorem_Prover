module Unification.RunUnificationTests where 

import Unification.FormulaContainsVarTests (runFormulaContainsVarTests)
import Unification.TermContainsVarTests (runTermContainsVarTests)
import Unification.StandardiseApartTests (runStandardiseApartTests)
import Unification.SubInListTests(runSubInListTests)
import Unification.TermUnificationTests(runTermUnificationTests)
import Unification.AtomUnificationTests (runAtomUnificationTests)
import Unification.UnifyTests (runUnifyTests)

runUnificationTests :: [Char]
runUnificationTests = concat 
    [
        "\n\n\n Running Unification Tests",
        runFormulaContainsVarTests,
        runTermContainsVarTests,
        runStandardiseApartTests,
        runSubInListTests,
        runTermUnificationTests,
        runAtomUnificationTests,
        runUnifyTests
    ]