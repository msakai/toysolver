{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- ------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Graph.ShortestPath
-- Copyright   :  (c) Masahiro Sakai 2016-2017
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- ------------------------------------------------------------------------
module ToySolver.Graph.ShortestPath
  (
  -- * Edge data types
    Edge
  , OutEdge
  , InEdge

  -- * Path data types
  , Path (..)
  , pathFrom
  , pathTo
  , pathCost
  , pathEmpty
  , pathAppend
  , pathEdges
  , pathEdgesBackward
  , pathEdgesSeq
  , pathVertexes
  , pathVertexesBackward
  , pathVertexesSeq

  -- * Shortest-path algorithms
  , bellmanFord
  , dijkstra
  , floydWarshall

  -- * Utility functions
  , buildPaths
  ) where

import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Data.Hashable
import qualified Data.HashTable.Class as H
import qualified Data.HashTable.ST.Cuckoo as C
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashMap.Lazy as HashMapLazy
import qualified Data.HashSet as HashSet
import qualified Data.Heap as Heap -- http://hackage.haskell.org/package/heaps
import Data.List (foldl')
import Data.Maybe
import Data.Monoid
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.STRef

-- ------------------------------------------------------------------------

type Edge vertex cost label = (vertex, vertex, cost, label)

type OutEdge vertex cost label = (vertex, cost, label)

type InEdge vertex cost label = (vertex, cost, label)

data Path vertex cost label 
  = Empty vertex
  | Singleton (Edge vertex cost label)
  | Append (Path vertex cost label) (Path vertex cost label) !cost
  deriving (Eq, Show)

pathFrom :: Path vertex cost label -> vertex
pathFrom (Empty v) = v
pathFrom (Singleton (from,_,_,_)) = from
pathFrom (Append p1 _ _) = pathFrom p1

pathTo :: Path vertex cost label -> vertex
pathTo (Empty v) = v
pathTo (Singleton (_,to,_,_)) = to
pathTo (Append _ p2 _) = pathTo p2

pathCost :: Num cost => Path vertex cost label -> cost
pathCost (Empty _) = 0
pathCost (Singleton (_,_,c,_)) = c
pathCost (Append _ _ c) = c

pathEmpty :: vertex -> Path vertex cost label
pathEmpty = Empty

pathAppend :: (Eq vertex, Num cost) => Path vertex cost label -> Path vertex cost label -> Path vertex cost label
pathAppend p1 p2 
  | pathTo p1 /= pathFrom p2 = error "ToySolver.Graph.ShortestPath.pathAppend: pathTo/pathFrom mismatch"
  | otherwise =
      case (p1, p2) of
        (Empty _, _) -> p2
        (_, Empty _) -> p1
        _ -> Append p1 p2 (pathCost p1 + pathCost p2)

pathEdges :: Path vertex cost label -> [Edge vertex cost label]
pathEdges p = f p []
  where
    f (Empty _) xs = xs
    f (Singleton e) xs = e : xs
    f (Append p1 p2 _) xs = f p1 (f p2 xs)

pathEdgesBackward :: Path vertex cost label -> [Edge vertex cost label]
pathEdgesBackward p = f p []
  where
    f (Empty _) xs = xs
    f (Singleton e) xs = e : xs
    f (Append p1 p2 _) xs = f p2 (f p1 xs)

pathEdgesSeq :: Path vertex cost label -> Seq (Edge vertex cost label)
pathEdgesSeq (Empty _) = Seq.empty
pathEdgesSeq (Singleton e) = Seq.singleton e
pathEdgesSeq (Append p1 p2 _) = pathEdgesSeq p1 <> pathEdgesSeq p2

pathVertexes :: Path vertex cost label -> [vertex]
pathVertexes p = pathFrom p : f p []
  where
    f (Empty _) xs = xs
    f (Singleton (_,v2,_,_)) xs = v2 : xs
    f (Append p1 p2 _) xs = f p1 (f p2 xs)

pathVertexesBackward :: Path vertex cost label -> [vertex]
pathVertexesBackward p = pathTo p : f p []
  where
    f (Empty _) xs = xs
    f (Singleton (v1,_,_,_)) xs = v1 : xs
    f (Append p1 p2 _) xs = f p2 (f p1 xs)

pathVertexesSeq :: Path vertex cost label -> Seq vertex
pathVertexesSeq p = f True p
  where
    f True  (Empty v) = Seq.singleton v
    f False (Empty _) = mempty
    f True  (Singleton (v1,v2,_,_)) = Seq.fromList [v1, v2]
    f False (Singleton (v1,_,_,_))  = Seq.singleton v1
    f b (Append p1 p2 _) = f False p1 <> f b p2

pathMin :: (Num cost, Ord cost) => Path vertex cost label -> Path vertex cost label -> Path vertex cost label
pathMin p1 p2
  | pathCost p1 <= pathCost p2 = p1
  | otherwise = p2

-- ------------------------------------------------------------------------

-- | Bellman-Ford algorithm for finding shortest paths from source vertexes
-- to all of the other vertices in a weighted graph with negative weight
-- edges allowed.
--
-- Reference:
--
-- * Friedrich Eisenbrand. “Linear and Discrete Optimization”.
--   <https://www.coursera.org/course/linearopt>
bellmanFord
  :: (Eq vertex, Hashable vertex, Real cost)
  => HashMap vertex [OutEdge vertex cost label]
  -> [vertex] -- ^ list of source vertexes
  -> Either (Path vertex cost label) (HashMap vertex (cost, Maybe (InEdge vertex cost label)))
bellmanFord g ss = runST $ do
  let n = HashMap.size g
  d <- C.newSized n
  forM_ ss $ \s -> H.insert d s (0, Nothing)

  updatedRef <- newSTRef (HashSet.fromList ss)
  _ <- runExceptT $ replicateM_ n $ do
    us <- lift $ readSTRef updatedRef
    when (HashSet.null us) $ throwE ()
    lift $ do
      writeSTRef updatedRef HashSet.empty
      forM_ (HashSet.toList us) $ \u -> do
        Just (du, _) <- H.lookup d u
        forM_ (HashMap.lookupDefault [] u g) $ \(v, c, l) -> do
          m <- H.lookup d v
          case m of
            Just (c0, _) | c0 <= du + c -> return ()
            _ -> do
              H.insert d v (du + c, Just (u,c,l))
              modifySTRef' updatedRef (HashSet.insert v)

  xs <- H.toList d
  runExceptT $ do
    forM_ xs $ \(u,(du,_)) ->
      forM_ (HashMap.lookupDefault [] u g) $ \(v, c, l) -> do
        Just (dv,_) <- lift $ H.lookup d v
        when (du + c < dv) $ do
          -- a negative cycle is detected
          cyclePath <- lift $ do
            H.insert d v (du + c, Just (u, c, l))
            u0 <- do
              let getParent u = do
                    Just (_, Just (v,_,_)) <- H.lookup d u
                    return v
                  go hare tortoise
                    | hare == tortoise = return hare
                    | otherwise = do
                        hare' <- getParent =<< getParent hare
                        tortoise' <- getParent tortoise
                        go hare' tortoise'
              hare0 <- getParent =<< getParent v
              tortoise0 <- getParent v
              go hare0 tortoise0
            let go u result = do
                  Just (_, Just (v,c,l)) <- H.lookup d u
                  if v == u0 then
                    return (Singleton (v,u,c,l) `pathAppend` result)
                  else
                    go v (Singleton (v,u,c,l) `pathAppend` result)
            go u0 (pathEmpty u0)
          throwE cyclePath
    d' <- lift $ freezeHashTable d
    return d'

freezeHashTable :: (H.HashTable h, Hashable k, Eq k) => h s k v -> ST s (HashMap k v)
freezeHashTable h = H.foldM (\m (k,v) -> return $! HashMap.insert k v m) HashMap.empty h

-- ------------------------------------------------------------------------

-- | Dijkstra's algorithm for finding shortest paths from source vertexes
-- to all of the other vertices in a weighted graph with non-negative edge
-- weight.
dijkstra
  :: forall vertex cost label. (Eq vertex, Hashable vertex, Real cost)
  => HashMap vertex [OutEdge vertex cost label]
  -> [vertex] -- ^ list of source vertexes
  -> HashMap vertex (cost, Maybe (InEdge vertex cost label))
dijkstra g ss = loop (Heap.fromList [Heap.Entry 0 (s, Nothing) | s <- ss]) HashMap.empty
  where
    loop
      :: Heap.Heap (Heap.Entry cost (vertex, Maybe (InEdge vertex cost label)))
      -> HashMap vertex (cost, Maybe (InEdge vertex cost label))
      -> HashMap vertex (cost, Maybe (InEdge vertex cost label))
    loop q visited =
      case Heap.viewMin q of
        Nothing -> visited
        Just (Heap.Entry c (v, m), q')
          | v `HashMap.member` visited -> loop q' visited
          | otherwise ->
              let q2 = Heap.fromList
                       [ Heap.Entry (c+c') (ch, Just (v,c',l))
                       | (ch,c',l) <- HashMap.lookupDefault [] v g
                       , not (ch `HashMap.member` visited)
                       ]
              in loop (Heap.union q' q2) (HashMap.insert v (c, m) visited)

-- ------------------------------------------------------------------------

-- | Floyd-Warshall algorithm for finding shortest paths in a weighted graph
-- with positive or negative edge weights (but with no negative cycles).
floydWarshall
  :: forall vertex cost label. (Eq vertex, Hashable vertex, Real cost)
  => HashMap vertex [OutEdge vertex cost label]
  -> HashMap (vertex,vertex) (Path vertex cost label)
floydWarshall g = HashMap.unionWith pathMin (foldl' f tbl0 vs) paths0
  where
    vs = HashMap.keys g

    paths0 :: HashMap (vertex,vertex) (Path vertex cost label)
    paths0 = HashMap.fromList [((v,v), pathEmpty v) | v <- HashMap.keys g]

    tbl0 :: HashMap (vertex,vertex) (Path vertex cost label)
    tbl0 = HashMap.fromListWith pathMin [((v,u), Singleton (v,u,c,l)) | (v, es) <- HashMap.toList g, (u,c,l) <- es]

    f :: HashMap (vertex,vertex) (Path vertex cost label)
      -> vertex
      -> HashMap (vertex,vertex) (Path vertex cost label)
    f tbl vk = HashMap.unionWith pathMin tbl tbl'
      where
        tbl' = HashMap.fromList
          [ ((vi,vj), pathAppend p1 p2)
          | vi <- vs, p1 <- maybeToList (HashMap.lookup (vi,vk) tbl)
          , vj <- vs, p2 <- maybeToList (HashMap.lookup (vk,vj) tbl)
          ]

-- ------------------------------------------------------------------------

buildPaths
  :: (Eq vertex, Hashable vertex, Real cost)
  => HashMap vertex (cost, Maybe (InEdge vertex cost label))
  -> HashMap vertex (Path vertex cost label)
buildPaths m = paths
  where
    paths = HashMapLazy.mapWithKey f m
    f u (_, Nothing) = pathEmpty u
    f u (_, Just (v,c,l)) = (paths HashMap.! v) `pathAppend` Singleton (v,u,c,l)

-- ------------------------------------------------------------------------
