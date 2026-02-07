module Subsumption.SubsumptionFilter 
    (
        getSymbolOrder, 
        getFeatureVector,
        emptyClauseTrie,
        insertInClauseTrie,
        retrieveAllPossiblySubsumingClauses,
        ClauseTrie(..)
    ) where


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


-- A Feature Vector maps a symbol to its frequency in a clause
type FeatureVector = Map String Int

data ClauseTrie = ClauseTrieNode
    {
        values :: [Clause],
        children :: Map Int ClauseTrie
    } deriving (Eq, Show)

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

-- Returns all clauses that may subsume the clause represented by this feature vector 
retrieveAllPossiblySubsumingClauses :: [String] -> FeatureVector -> ClauseTrie -> [Clause]
retrieveAllPossiblySubsumingClauses [] _ (ClauseTrieNode clauses _) = clauses
retrieveAllPossiblySubsumingClauses (symbol: symbols) featureVector (ClauseTrieNode clauses children) =
    clauses ++ results
    where 
        symbolCount = Map.findWithDefault 0 symbol featureVector
        branches = Map.filterWithKey (\frequency _ -> frequency <= symbolCount) children
        results = concatMap (retrieveAllPossiblySubsumingClauses symbols featureVector) (Map.elems branches)