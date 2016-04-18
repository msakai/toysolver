{-# OPTIONS_GHC #-}
{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Combinatorial.MaximumCardinalityBipartiteMatching
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables)
--
-- Reference:
--
-- * Friedrich Eisenbrand. “Linear and Discrete Optimization”.
--   <https://www.coursera.org/course/linearopt>
--
-----------------------------------------------------------------------------
module ToySolver.Combinatorial.MaximumCardinalityBipartiteMatching
  ( solve
  , solve'
  ) where

import Data.Foldable (toList)
import Data.Hashable
import Data.HashMap.Strict (HashMap, (!))
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Monoid

solve
  :: forall a b. (Hashable a, Eq a, Hashable b, Eq b)
  => HashSet a -> HashSet b -> HashSet (a,b) -> HashSet (a,b)
solve as bs es = 
  case solve' as bs (\b -> HashMap.lookupDefault HashSet.empty b e_b2a) HashMap.empty of
    (m, _, _) -> HashSet.fromList $ HashMap.toList m
  where
    e_b2a :: HashMap b (HashSet a)
    e_b2a = HashMap.fromListWith HashSet.union [(b, HashSet.singleton a) | (a,b) <- HashSet.toList es]

-- | Internal low-level routine for maximum cardinality bipartite matching.
--
-- It returns a maximum cardinality matching M together with sets of
-- vertexes reachable from exposed B vertexes (b∈B such that ∀a∈A. (a,b)∉M)
-- on a directed graph of (A∪B, {a→b|(a,b)∈M}∪{b→a|(a,b)⊆E\\M}).
solve'
  :: forall a b. (Hashable a, Eq a, Hashable b, Eq b)
  => HashSet a        -- ^ vertex set A
  -> HashSet b        -- ^ vertex set B
  -> (b -> HashSet a) -- ^ set of edges E⊆A×B represented as a mapping from B to 2^A.
  -> HashMap a b      -- ^ partial matching represented as an injective mapping from A to B
  -> (HashMap a b, HashSet a, HashSet b)
solve' as bs e_b2a m0 = loop m0 m0_b_exposed
  where
    m0_b_exposed = bs `HashSet.difference` HashSet.fromList [b | (_,b) <- HashMap.toList m0]

    loop :: HashMap a b -> HashSet b -> (HashMap a b, HashSet a, HashSet b)
    loop m m_b_exposed =
      case search m_b_exposed of
        Left (l_a, l_b) -> (m, l_a, l_b)
        Right d2 ->
          let -- Note that HashMap.union is left-biased
              m' = HashMap.fromList d2 `HashMap.union` m
              m_b_exposed' = HashSet.delete (snd (last d2)) m_b_exposed
          in loop m' m_b_exposed'
      where
        search :: HashSet b -> Either (HashSet a, HashSet b) [(a,b)]
        search b_exposed = loopB HashSet.empty b_exposed [(b, []) | b <- HashSet.toList b_exposed] []
          where
            loopB :: HashSet a -> HashSet b -> [(b, [(a,b)])] -> [(b, [(a,b)])] -> Either (HashSet a, HashSet b) [(a,b)]
            loopB !visitedA !visitedB [] [] = Left (visitedA, visitedB)
            loopB !visitedA !visitedB [] nextB = loopB visitedA visitedB nextB []
            loopB !visitedA !visitedB ((b, d2) : currB) nextB = loopA visitedA visitedB (HashSet.toList (e_b2a b)) currB nextB
              where
                loopA !visitedA !visitedB [] currB nextB = loopB visitedA visitedB currB nextB
                loopA !visitedA !visitedB (a:as) currB nextB
                  | a `HashSet.member` visitedA = loopA visitedA visitedB as currB nextB
                  | otherwise =
                      case HashMap.lookup a m of
                        Nothing -> Right ((a,b) : d2)
                        Just b2
                          | b==b2 -> loopA visitedA visitedB as currB nextB
                          | b2 `HashSet.member` visitedB -> loopA (HashSet.insert a visitedA) visitedB as currB nextB
                          | otherwise -> loopA (HashSet.insert a visitedA) (HashSet.insert b2 visitedB) as currB ((b2, (a,b2):(a,b):d2) : nextB)

test = solve as bs es
  where
    as = HashSet.fromList ['a'..'e']
    bs :: HashSet Int
    bs = HashSet.fromList [1..5]
    es = HashSet.fromList [(a,b) | a <- HashSet.toList as, b <- HashSet.toList bs]
