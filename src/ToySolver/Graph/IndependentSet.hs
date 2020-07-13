{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
module ToySolver.Graph.IndependentSet
  ( Graph
  , edges
  , graphFromEdges
  , isIndependentSet
  ) where

import Control.Monad
import Data.Array.IArray
import Data.Array.ST
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)

type Graph = Array Int IntSet

edges :: Graph -> [(Int, Int)]
edges g = do
  (node1, nodes) <- assocs g
  node2 <- IntSet.toList $ snd $ IntSet.split node1 nodes
  return (node1, node2)

graphFromEdges :: Int -> [(Int, Int)] -> Graph
graphFromEdges n es = runSTArray $ do
  a <- newArray (0, n-1) IntSet.empty
  let ins i x = do
        s <- readArray a i
        writeArray a i $! IntSet.insert x s
  forM_ es $ \(node1, node2) -> do
    ins node1 node2
    ins node2 node1
  return a

isIndependentSet :: Graph -> IntSet -> Bool
isIndependentSet g s = null $ do
  (node1, node2) <- edges g
  guard $ node1 `IntSet.member` s
  guard $ node2 `IntSet.member` s
  return ()
