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
  case solve' as bs (\b -> HashMap.lookupDefault HashSet.empty b e_b2a) HashSet.empty of
    (m, _, _) -> m
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
  -> (b -> HashSet a) -- ^ set of edges E⊆A×B represented  as a mapping from B to 2^A.
  -> HashSet (a,b)    -- ^ partial matching
  -> (HashSet (a,b), HashSet a, HashSet b)
solve' as bs e_b2a m0 = loop m0_a2b m0_b2a m0_b_exposed
  where
    m0_a2b = HashMap.fromList [(a,b) | (a,b) <- HashSet.toList m0]
    m0_b2a = HashMap.fromList [(b,a) | (a,b) <- HashSet.toList m0]
    m0_b_exposed = HashSet.filter (not . (`HashMap.member` m0_b2a)) bs

    loop :: HashMap a b -> HashMap b a -> HashSet b -> (HashSet (a,b), HashSet a, HashSet b)
    loop m_a2b m_b2a m_b_exposed =
      case search m_b_exposed of
        Left (l_a, l_b) ->
          ( HashSet.fromList $ HashMap.toList m_a2b
          , l_a
          , l_b
          )
        Right d2 ->
          let -- Note that HashMap.union is left-biased
              m_a2b' = HashMap.fromList d2 `HashMap.union` m_a2b
              m_b2a' = HashMap.fromList [(b,a) | (a,b) <- d2] `HashMap.union` m_b2a
              m_b_exposed' = HashSet.delete (snd (last d2)) m_b_exposed
          in loop m_a2b' m_b2a' m_b_exposed'
      where
        search :: HashSet b -> Either (HashSet a, HashSet b) [(a,b)]
        search bs = loopB HashSet.empty bs [] [(b, []) | b <- HashSet.toList bs]
          where
            loopA :: HashSet a -> HashSet b -> [(a, [(a,b)])] -> [(b, [(a,b)])] -> Either (HashSet a, HashSet b) [(a,b)]
            loopA !visitedA !visitedB currA currB =
              case currA of
                []
                  | null currB -> Left (visitedA, visitedB)
                  | otherwise -> loopB visitedA visitedB [] currB 
                (a, d2) : currA'
                  | a `HashSet.member` visitedA -> loopA visitedA visitedB currA' currB
                  | otherwise ->
                      case HashMap.lookup a m_a2b of
                        Nothing -> Right d2
                        Just b
                          | b `HashSet.member` visitedB -> loopA (HashSet.insert a visitedA) visitedB currA' currB
                          | otherwise -> loopA (HashSet.insert a visitedA) (HashSet.insert b visitedB) currA' ((b, d2) : currB)
            loopB :: HashSet a -> HashSet b -> [(a, [(a,b)])] -> [(b, [(a,b)])] -> Either (HashSet a, HashSet b) [(a,b)]
            loopB !visitedA !visitedB currA currB =
              case currB of
                []
                  | null currA -> Left (visitedA, visitedB)
                  | otherwise -> loopA visitedA visitedB currA []
                (b, d2) : currB' ->
                  loopB visitedA (HashSet.insert b visitedB)
                    ([(a, (a,b):d2) | a <- HashSet.toList as3] ++ currA)
                    currB'
                  where
                    as2 = e_b2a b
                    as3 = case HashMap.lookup b m_b2a of
                            Nothing -> as2
                            Just a -> HashSet.delete a as2

test = solve as bs es
  where
    as = HashSet.fromList ['a'..'e']
    bs :: HashSet Int
    bs = HashSet.fromList [1..5]
    es = HashSet.fromList [(a,b) | a <- HashSet.toList as, b <- HashSet.toList bs]
