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
import Data.Sequence (Seq, ViewL (..))
import qualified Data.Sequence as Seq
import ToySolver.BellmanFord

solve
  :: forall a b. (Hashable a, Eq a, Hashable b, Eq b)
  => HashSet a -> HashSet b -> HashSet (a,b) -> HashSet (a,b)
solve as bs es = solve' as bs es HashSet.empty

solve'
  :: forall a b. (Hashable a, Eq a, Hashable b, Eq b)
  => HashSet a -> HashSet b -> HashSet (a,b) -> HashSet (a,b) -> HashSet (a,b)
solve' as bs es = loop
  where
    loop :: HashSet (a,b) -> HashSet (a,b)
    loop m =
      case search HashSet.empty HashSet.empty (Seq.fromList [(Right b, [], []) | b <- HashSet.toList b_exposed]) of
        Nothing -> m
        Just (d1, d2) ->
          loop $! (m `HashSet.difference` (HashSet.fromList d1)) `HashSet.union` HashSet.fromList d2
      where
        a_exposed = as `HashSet.difference` HashSet.map (\(a,b) -> a) m
        b_exposed = bs `HashSet.difference` HashSet.map (\(a,b) -> b) m

        a2b :: HashMap a (Seq b)
        a2b = HashMap.fromListWith (<>) [(a, Seq.singleton b) | (a,b) <- HashSet.toList m]

        b2a :: HashMap b (Seq a)
        b2a = HashMap.fromListWith (<>) [(b, Seq.singleton a) | e@(a,b) <- HashSet.toList es, not (e `HashSet.member` m)]

        search :: HashSet a -> HashSet b -> Seq (Either a b, [(a,b)], [(a,b)]) -> Maybe ([(a,b)], [(a,b)])
        search !visitedA !visitedB curr =
          case Seq.viewl curr of
            Seq.EmptyL -> Nothing
            (Left a, d1, d2) :< curr'
              | a `HashSet.member` visitedA -> search visitedA visitedB curr'
              | a `HashSet.member` a_exposed -> Just $ (d1,d2)
              | otherwise ->
                  search (HashSet.insert a visitedA) visitedB
                         (curr' <> fmap (\b -> (Right b, (a,b):d1, d2)) (HashMap.lookupDefault Seq.empty a a2b))
            (Right b, d1, d2) :< curr'
              | b `HashSet.member` visitedB -> search visitedA visitedB curr'
              | otherwise ->
                  search visitedA (HashSet.insert b visitedB)
                         (curr' <> fmap (\a -> (Left a, d1, (a,b):d2)) (HashMap.lookupDefault Seq.empty b b2a))

test = solve as bs es
  where
    as = HashSet.fromList ['a'..'e']
    bs :: HashSet Int
    bs = HashSet.fromList [1..5]
    es = HashSet.fromList [(a,b) | a <- HashSet.toList as, b <- HashSet.toList bs]
