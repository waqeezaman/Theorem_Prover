module Subsumption.SubsumptionFilter where


import Data.Map (Map)
import qualified Data.Map as Map
import FOL (Clause (..), Literal (..), Predicate (..), Term (..))
import Data.List (nub, sort)

funcConst :: String
funcConst = "_F_"
predConst :: String
predConst = "_P_"
negLiteralConst :: String
negLiteralConst = "_¬_"

data SubsumptionProofState = SubsumptionProofState
    {
        symbolOrdering :: [String],
        clauseTrie :: ClauseTrie
    }

-- The feature vector should really be a list of int
-- following a strict ordering on symbols 
-- Where each int represents the frequency of a term

-- A Feature Vector maps a Symbol (String) to its frequency in a clause
type FeatureVector = Map String Int

-- getFeatureVectorList :: FeatureVector -> [String] -> [Int] -> [Int]
-- getFeatureVectorList vector [] 


getSymbolOrder :: [Clause] -> [String]
getSymbolOrder clauses = sort $ nub $ concatMap extractSymbolsFromClause clauses

-- Extract features from a Clause (assuming a Clause is a list of Literals)
-- and a Literal is a predicate with terms.
getFeatureVector :: Clause -> FeatureVector
getFeatureVector clause = Map.fromListWith (+) [(s, 1) | s <- extractSymbolsFromClause clause]

extractSymbolsFromClause :: Clause ->  [String]
extractSymbolsFromClause (Clause literals) = concatMap extractSymbolsFromLiteral literals

extractSymbolsFromTerm :: Term -> [String]
extractSymbolsFromTerm (Var _) = []
extractSymbolsFromTerm (Fn(f, subterms)) = (funcConst++f) : concatMap extractSymbolsFromTerm subterms

extractSymbolsFromLiteral :: Literal -> [String]
extractSymbolsFromLiteral (Pos (R(p, terms))) = (predConst++p) : concatMap extractSymbolsFromTerm terms
extractSymbolsFromLiteral (Neg (R(p, terms))) = (negLiteralConst++predConst++p) : concatMap extractSymbolsFromTerm terms


-- Subsumption check pre-filter: 
-- Returns True if 'c' COULD potentially subsume 'd'.
containsSubsetOfSymbols :: FeatureVector -> FeatureVector -> Bool
containsSubsetOfSymbols = Map.isSubmapOfBy (<=)


data ClauseTrie = ClauseTrieNode
    {
        values :: [Clause],
        children :: Map Int ClauseTrie
    } deriving (Eq, Show)

emptyClauseTrie :: ClauseTrie
emptyClauseTrie = ClauseTrieNode [] Map.empty


insertInClauseTrie :: [String] -> Clause -> FeatureVector -> ClauseTrie -> ClauseTrie
insertInClauseTrie [] clause _ (ClauseTrieNode clauses children) = ClauseTrieNode (clause:clauses) children
insertInClauseTrie (symbol:symbols) clause featureVector (ClauseTrieNode clauses children) = 
    ClauseTrieNode clauses (Map.insert frequency newBranch children)
    where 
        frequency = Map.findWithDefault 0 symbol featureVector
        branch = Map.findWithDefault emptyClauseTrie frequency children
        newBranch = insertInClauseTrie symbols clause featureVector  branch


retrieveAllSubsumingClauses :: [String] -> FeatureVector -> ClauseTrie -> [Clause]
retrieveAllSubsumingClauses [] _ (ClauseTrieNode clauses _) = clauses
retrieveAllSubsumingClauses (symbol: symbols) featureVector (ClauseTrieNode clauses children) =
    clauses ++ results
    where 
        symbolCount = Map.findWithDefault 0 symbol featureVector
        branches = Map.filterWithKey (\frequency _ -> frequency <= symbolCount) children
        results = concatMap (retrieveAllSubsumingClauses symbols featureVector) (Map.elems branches)