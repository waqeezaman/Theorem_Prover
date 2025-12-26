-- useful utils to add 
-- alpha equivalencee 
-- pushing connectives to the right 
-- e.g. (A AND B) AND C  -> A AND (B AND C)
-- gives us a standardised way to deal with connectives 
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Utils (transitiveClosure) where 

import qualified Data.Map as Map

-- Returns the transitive closure of a Map
transitiveClosure :: Ord k => Map.Map k k -> Map.Map k k
transitiveClosure sub = Map.map (transitiveClosure' sub) sub

transitiveClosure' :: Ord t => Map.Map t t -> t -> t
transitiveClosure' map x =
    case mapping of 
        Just t -> transitiveClosure' map t 
        Nothing -> x
    where mapping = Map.lookup x map