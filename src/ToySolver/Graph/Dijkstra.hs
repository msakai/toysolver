{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- ------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Graph.Dijkstra
-- Copyright   :  (c) Masahiro Sakai 2017
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Dijkstra's algorithm for finding shortest paths from source vertexes
-- to all of the other vertices in a weighted graph with non-negative edge
-- weight.
--
-- ------------------------------------------------------------------------
module ToySolver.Graph.Dijkstra
  ( dijkstra
  ) where

import Data.Hashable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Heap as H -- http://hackage.haskell.org/package/heaps

dijkstra
  :: forall vertex cost label. (Eq vertex, Hashable vertex, Real cost)
  => HashMap vertex [(vertex, cost, label)]
  -> [vertex] -- ^ list of source vertexes
  -> HashMap vertex (cost, Maybe (vertex, label))
dijkstra g ss = loop (H.fromList [H.Entry 0 (s, Nothing) | s <- ss]) HashMap.empty
  where
    loop
      :: H.Heap (H.Entry cost (vertex, Maybe (vertex, label)))
      -> HashMap vertex (cost, Maybe (vertex, label))
      -> HashMap vertex (cost, Maybe (vertex, label))
    loop q visited =
      case H.viewMin q of
        Nothing -> visited
        Just (H.Entry c (v, m), q')
          | v `HashMap.member` visited -> loop q' visited
          | otherwise ->
              let q2 = H.fromList
                       [ H.Entry (c+c') (ch, Just (v,l))
                       | (ch,c',l) <- HashMap.lookupDefault [] v g
                       , not (ch `HashMap.member` visited)
                       ]
              in loop (H.union q' q2) (HashMap.insert v (c, m) visited)
