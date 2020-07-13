{-# LANGUAGE FlexibleContexts #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Graph.Base
-- Copyright   :  (c) Masahiro Sakai 2020
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Graph.Base
  ( EdgeLabeledGraph
  , Graph
  , graphToUnorderedEdges
  , graphFromUnorderedEdges
  , graphFromUnorderedEdgesWith
  , isIndependentSet
  ) where

import Control.Monad
import Data.Array.IArray
import Data.Array.ST
import qualified Data.IntMap.Lazy as IntMap
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)

type EdgeLabeledGraph a = Array Int (IntMap a)

type Graph = EdgeLabeledGraph ()

graphToUnorderedEdges :: EdgeLabeledGraph a -> [(Int, Int, a)]
graphToUnorderedEdges g = do
  (node1, nodes) <- assocs g
  (node2, a) <- IntMap.toList $ snd $ IntMap.split node1 nodes
  return (node1, node2, a)

graphFromUnorderedEdges :: Int -> [(Int, Int, a)] -> EdgeLabeledGraph a
graphFromUnorderedEdges = graphFromUnorderedEdgesWith const

graphFromUnorderedEdgesWith :: (a -> a -> a) -> Int -> [(Int, Int, a)] -> EdgeLabeledGraph a
graphFromUnorderedEdgesWith f n es = runSTArray $ do
  a <- newArray (0, n-1) IntMap.empty
  let ins i x l = do
        m <- readArray a i
        writeArray a i $! IntMap.insertWith f x l m
  forM_ es $ \(node1, node2, a) -> do
    ins node1 node2 a
    ins node2 node1 a
  return a

isIndependentSet :: EdgeLabeledGraph a -> IntSet -> Bool
isIndependentSet g s = null $ do
  (node1, node2, _) <- graphToUnorderedEdges g
  guard $ node1 `IntSet.member` s
  guard $ node2 `IntSet.member` s
  return ()
