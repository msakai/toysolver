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
  (
  -- * Graph data types
    EdgeLabeledGraph
  , Graph
  , Vertex
  , VertexSet
  , Edge

  -- * Conversion

  -- ** Directed graphs
  , graphFromEdges
  , graphFromEdgesWith
  , graphToEdges

  -- ** Undirected graphs
  , graphFromUnorderedEdges
  , graphFromUnorderedEdgesWith
  , graphToUnorderedEdges

  -- * Operations
  , converseGraph
  , complementGraph
  , complementSimpleGraph

  -- * Properties
  , numVertexes
  , isSimpleGraph
  , isIndependentSet
  , isIndependentSetOf
  , isCliqueOf
  ) where

import Control.Monad
import Data.Array.IArray
import Data.Array.ST
import qualified Data.IntMap.Lazy as IntMap
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import Data.Maybe (maybeToList)
import GHC.Stack (HasCallStack)

-- | Labelled directed graph without multiple edges
--
-- We also represent undirected graphs as symmetric directed graphs.
type EdgeLabeledGraph a = Array Vertex (IntMap a)

-- | Directed graph without multiple edges
--
-- We also represent undirected graphs as symmetric directed graphs.
type Graph = EdgeLabeledGraph ()

-- | Vertex data type
type Vertex = Int

-- | Set of vertexes
type VertexSet = IntSet

-- | Edge data type
type Edge a = (Vertex, Vertex, a)

-- | Set of edges of directed graph
graphToEdges :: EdgeLabeledGraph a -> [Edge a]
graphToEdges g = do
  (node1, nodes) <- assocs g
  (node2, a) <- IntMap.toList nodes
  return (node1, node2, a)

-- | Construct a directed graph from edges.
--
-- If there are multiple edges with the same starting and ending
-- vertexes, the last label is used.
graphFromEdges :: HasCallStack => Int -> [Edge a] -> EdgeLabeledGraph a
graphFromEdges = graphFromEdgesWith const

-- | Construct a directed graph from edges.
--
-- If there are multiple edges with the same starting and ending
-- vertexes, the labels are combined using the given function.
graphFromEdgesWith :: HasCallStack => (a -> a -> a) -> Int -> [Edge a] -> EdgeLabeledGraph a
graphFromEdgesWith _ n _ | n < 0 = error "graphFromEdgesWith: number of vertexes should be non-negative"
graphFromEdgesWith f n es = runSTArray $ do
  g <- newArray (0, n-1) IntMap.empty
  forM_ es $ \(node1, node2, a) -> do
    m <- readArray g node1
    writeArray g node1 $! IntMap.insertWith f node2 a m
  return g

-- | Set of edges of undirected graph represented as a symmetric directed graph.
graphToUnorderedEdges :: EdgeLabeledGraph a -> [Edge a]
graphToUnorderedEdges g = do
  (node1, nodes) <- assocs g
  case IntMap.splitLookup node1 nodes of
    (_, m, nodes2) ->
      [(node1, node1, a) | a <- maybeToList m] ++
      [(node1, node2, a) | (node2, a) <- IntMap.toList nodes2]

-- | Construct a symmetric directed graph from unordered edges.
--
-- If there are multiple edges with the same starting and ending
-- vertexes, the last label is used.
graphFromUnorderedEdges :: HasCallStack => Int -> [Edge a] -> EdgeLabeledGraph a
graphFromUnorderedEdges = graphFromUnorderedEdgesWith const

-- | Construct a symmetric directed graph from unordered edges.
--
-- If there are multiple edges with the same starting and ending
-- vertexes, the labels are combined using the given function.
graphFromUnorderedEdgesWith :: HasCallStack => (a -> a -> a) -> Int -> [Edge a] -> EdgeLabeledGraph a
graphFromUnorderedEdgesWith _ n _ | n < 0 = error "graphFromUnorderedEdgesWith: number of vertexes should be non-negative"
graphFromUnorderedEdgesWith f n es = runSTArray $ do
  a <- newArray (0, n-1) IntMap.empty
  let ins i x l = do
        m <- readArray a i
        writeArray a i $! IntMap.insertWith f x l m
  forM_ es $ \(node1, node2, a) -> do
    ins node1 node2 a
    unless (node1 == node2) $ ins node2 node1 a
  return a

-- | Converse of a graph.
--
-- It returns another directed graph on the same set of vertices with all of the edges reversed.
-- This is also called /transpose/ or /reverse/ of a graph.
converseGraph :: EdgeLabeledGraph a -> EdgeLabeledGraph a
converseGraph g = graphFromEdges (numVertexes g) [(n2, n1, l) | (n1, n2, l) <- graphToEdges g]

-- | Complement of a graph
--
-- Note that applying it to a graph with no self-loops results in a graph with self-loops on all vertices.
complementGraph :: EdgeLabeledGraph a -> EdgeLabeledGraph ()
complementGraph g = array (bounds g) [(node, toAllNodes IntMap.\\ outEdges) | (node, outEdges) <- assocs g]
  where
    toAllNodes = IntMap.fromAscList [(node, ()) | node <- indices g]

-- | Complement of a simple graph
--
-- It ignores self-loops in the input graph and also does not add self-loops to the output graph.
complementSimpleGraph :: EdgeLabeledGraph a -> EdgeLabeledGraph ()
complementSimpleGraph g = array (bounds g) [(node, IntMap.delete node toAllNodes IntMap.\\ outEdges) | (node, outEdges) <- assocs g]
  where
    toAllNodes = IntMap.fromAscList [(node, ()) | node <- indices g]

-- | Number of vertexes of a graph
numVertexes :: EdgeLabeledGraph a -> Int
numVertexes g =
  case bounds g of
    (lb, ub)
      | lb /= 0 -> error "numVertexes: lower bound should be 0"
      | otherwise -> ub + 1

-- | A graph is /simple/ if it contains no self-loops.
isSimpleGraph :: EdgeLabeledGraph a -> Bool
isSimpleGraph g = and [v `IntMap.notMember` es | (v, es) <- assocs g]

-- | Alias of 'isIndependentSetOf'
{-# DEPRECATED isIndependentSet "Use isIndependentSetOf instead" #-}
isIndependentSet :: EdgeLabeledGraph a -> VertexSet -> Bool
isIndependentSet = flip isIndependentSetOf

-- | An independent set of a graph is a set of vertices such that no two vertices in the set are adjacent.
--
-- This function ignores self-loops in the input graph.
isIndependentSetOf :: VertexSet -> EdgeLabeledGraph a -> Bool
isIndependentSetOf s g = null $ do
  (node1, node2, _) <- graphToUnorderedEdges g
  guard $ node1 `IntSet.member` s
  guard $ node2 `IntSet.member` s
  return ()

-- | A clique of a graph is a subset of vertices such that every two distinct vertices in the clique are adjacent.
isCliqueOf :: VertexSet -> EdgeLabeledGraph a -> Bool
isCliqueOf s g = all (\node -> IntSet.delete node s `IntSet.isSubsetOf` IntMap.keysSet (g ! node)) (IntSet.toList s)
