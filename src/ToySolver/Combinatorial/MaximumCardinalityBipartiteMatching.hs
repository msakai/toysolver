{-# LANGUAGE ScopedTypeVariables #-}
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

import Data.Hashable
import Data.HashMap.Strict (HashMap, (!))
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
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
      case bellmanford g ([Right b | b <- HashSet.toList b_exposed]) of
        Left _ -> error "MaximumCardinalityBipartiteMatching: should not happen"
        Right d ->
          case [a | a <- HashSet.toList a_exposed, Left a `HashMap.member` d] of
            [] -> m
            a : _ ->
              let path = constructPath d (Left a)
                  d1 = HashSet.fromList [(a,b) | (Left a, Right b) <- path]
                  d2 = HashSet.fromList [(a,b) | (Right b, Left a) <- path]
                  m' = (m `HashSet.difference` d1) `HashSet.union` d2
              in loop $! m'
      where
        g :: HashMap (Either a b) [(Either a b, Int, ())]
        g = HashMap.fromListWith (++) $
            [(Left a, [(Right b, 1, ())]) | (a,b) <- HashSet.toList m] ++
            [(Right b, [(Left a, 1, ())]) | (a,b) <- HashSet.toList (es `HashSet.difference` m)]
        a_exposed = as `HashSet.difference` HashSet.map (\(a,b) -> a) m
        b_exposed = bs `HashSet.difference` HashSet.map (\(a,b) -> b) m

constructPath
  :: (Hashable vertex, Eq vertex)
  => HashMap vertex (cost, Maybe (vertex, label)) -> vertex -> [(vertex,vertex)]
constructPath d v = loop v []
  where
    loop v path =
      case d ! v of
        (_, Nothing) -> path
        (_, Just (u,_)) -> loop u ((u,v) : path)

test = solve as bs es
  where
    as = HashSet.fromList ['a'..'e']
    bs :: HashSet Int
    bs = HashSet.fromList [1..5]
    es = HashSet.fromList [(a,b) | a <- HashSet.toList as, b <- HashSet.toList bs]
