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

  -- * Fold data type
  , Fold (..)
  , monoid'
  , monoid
  , unit
  , pair
  , path
  , firstOutEdge
  , lastInEdge

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
  , pathFold

  -- * Shortest-path algorithms
  , bellmanFord
  , dijkstra
  , floydWarshall

  -- * Utility functions
  , detectCycle
  ) where

import Control.Arrow ((&&&))
import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Data.Hashable
import qualified Data.HashTable.Class as H
import qualified Data.HashTable.ST.Cuckoo as C
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.Heap as Heap -- http://hackage.haskell.org/package/heaps
import Data.List (foldl')
import Data.Maybe
import Data.Monoid
import Data.Ord
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

pathFold :: Fold vertex cost label a -> Path vertex cost label -> a
pathFold (Fold fV fE fC) = h
  where
    h (Empty v) = fV v
    h (Singleton e) = fE e
    h (Append p1 p2 _) = fC (h p1) (h p2)

-- ------------------------------------------------------------------------

-- | Operations for folding edge information along with a path into a @r@ value.
--
-- @Fold vertex cost label r@ consists of three opetations:
--
-- * @vertex -> r@ corresponds to an empty path,
--
-- * @Edge vertex cost label -> r@ corresponds to a single edge, and
--
-- * @r -> r -> r@ corresponds to path concatenation.
--
data Fold vertex cost label r = Fold (vertex -> r) (Edge vertex cost label -> r) (r -> r -> r)

-- | Project `Edge` into a monoid value and fold using monoidal operation.
monoid' :: Monoid m => (Edge vertex cost label -> m) -> Fold vertex cost label m
monoid' f = Fold (\_ -> mempty) f mappend

-- | Similar to 'monoid'' but a /label/ is directly used as a monoid value.
monoid :: Monoid m => Fold vertex cost m m
monoid = monoid' (\(_,_,_,m) -> m)

-- | Ignore contents and return a unit value.
unit :: Fold vertex cost label ()
unit = monoid' (\_ -> ())

-- | Pairs two `Fold` into one that produce a tuple.
pair :: Fold vertex cost label a -> Fold vertex cost label b -> Fold vertex cost label (a,b)
pair (Fold fV1 fE1 fC1) (Fold fV2 fE2 fC2) =
  Fold (fV1 &&& fV2) (fE1 &&& fE2) (\(a1,b1) (a2,b2) -> (fC1 a1 a2, fC2 b1 b2))

-- | Construct a `Path` value.
path :: (Eq vertex, Num cost) => Fold vertex cost label (Path vertex cost label)
path = Fold pathEmpty Singleton pathAppend

-- | Compute cost of a path.
cost :: Num cost => Fold vertex cost label cost
cost = Fold (\_ -> 0) (\(_,_,c,_) -> c) (+)

-- | Get the first `OutEdge` of a path.
firstOutEdge :: Fold vertex cost label (First (OutEdge vertex cost label))
firstOutEdge = monoid' (\(_,v,c,l) -> First (Just (v,c,l)))

-- | Get the last `InEdge` of a path.
-- This is useful for constructing a /parent/ map of a spanning tree.
lastInEdge :: Fold vertex cost label (Last (InEdge vertex cost label))
lastInEdge = monoid' (\(v,_,c,l) -> Last (Just (v,c,l)))

-- ------------------------------------------------------------------------

-- | Bellman-Ford algorithm for finding shortest paths from source vertexes
-- to all of the other vertices in a weighted graph with negative weight
-- edges allowed.
--
-- It compute shortest-paths from given source vertexes, and folds edge
-- information along shortest paths using a given 'Fold' operation.
--
-- Reference:
--
-- * Friedrich Eisenbrand. “Linear and Discrete Optimization”.
--   <https://www.coursera.org/course/linearopt>
bellmanFord
  :: (Eq vertex, Hashable vertex, Real cost)
  => Fold vertex cost label a
  -> HashMap vertex [OutEdge vertex cost label]
  -> [vertex] -- ^ list of source vertexes
  -> HashMap vertex (cost, a)
bellmanFord (Fold fV fE fC) g ss = runST $ do
  let n = HashMap.size g
  d <- C.newSized n
  forM_ ss $ \s -> H.insert d s (0, fV s)

  updatedRef <- newSTRef (HashSet.fromList ss)
  _ <- runExceptT $ replicateM_ n $ do
    us <- lift $ readSTRef updatedRef
    when (HashSet.null us) $ throwE ()
    lift $ do
      writeSTRef updatedRef HashSet.empty
      forM_ (HashSet.toList us) $ \u -> do
        Just (du, a) <- H.lookup d u
        forM_ (HashMap.lookupDefault [] u g) $ \(v, c, l) -> do
          m <- H.lookup d v
          case m of
            Just (c0, _) | c0 <= du + c -> return ()
            _ -> do
              H.insert d v (du + c, a `fC` fE (u,v,c,l))
              modifySTRef' updatedRef (HashSet.insert v)

  freezeHashTable d

freezeHashTable :: (H.HashTable h, Hashable k, Eq k) => h s k v -> ST s (HashMap k v)
freezeHashTable h = H.foldM (\m (k,v) -> return $! HashMap.insert k v m) HashMap.empty h

detectCycle
  :: forall vertex cost label a. (Eq vertex, Hashable vertex, Real cost)
  => Fold vertex cost label a
  -> HashMap vertex [OutEdge vertex cost label]
  -> HashMap vertex (cost, Last (InEdge vertex cost label))
  -> Maybe a
detectCycle (Fold fV fE fC) g d = either Just (const Nothing) $ do
  forM_ (HashMap.toList d) $ \(u,(du,_)) ->
    forM_ (HashMap.lookupDefault [] u g) $ \(v, c, l) -> do
      let (dv,_) = d HashMap.! v
      when (du + c < dv) $ do
        -- a negative cycle is detected
        let d' = HashMap.insert v (du + c, Last (Just (u, c, l))) d
            parent u = do
              case HashMap.lookup u d' of
                Just (_, Last (Just (v,_,_))) -> v
                _ -> undefined
            u0 = go (parent (parent v)) (parent v)
              where
                go hare tortoise
                  | hare == tortoise = hare
                  | otherwise = go (parent (parent hare)) (parent tortoise)
        let go u result = do
              let Just (_, Last (Just (v,c,l))) = HashMap.lookup u d'
              if v == u0 then
                fC (fE (v,u,c,l)) result
              else
                go v (fC (fE (v,u,c,l)) result)
        Left $ go u0 (fV u0)

-- ------------------------------------------------------------------------

-- | Dijkstra's algorithm for finding shortest paths from source vertexes
-- to all of the other vertices in a weighted graph with non-negative edge
-- weight.
--
-- It compute shortest-paths from given source vertexes, and folds edge
-- information along shortest paths using a given 'Fold' operation.
dijkstra
  :: forall vertex cost label a. (Eq vertex, Hashable vertex, Real cost)
  => Fold vertex cost label a
  -> HashMap vertex [OutEdge vertex cost label]
  -> [vertex] -- ^ list of source vertexes
  -> HashMap vertex (cost, a)
dijkstra (Fold fV fE fC) g ss = loop (Heap.fromList [Heap.Entry 0 (s, fV s) | s <- ss]) HashMap.empty
  where
    loop
      :: Heap.Heap (Heap.Entry cost (vertex, a))
      -> HashMap vertex (cost, a)
      -> HashMap vertex (cost, a)
    loop q visited =
      case Heap.viewMin q of
        Nothing -> visited
        Just (Heap.Entry c (v, a), q')
          | v `HashMap.member` visited -> loop q' visited
          | otherwise ->
              let q2 = Heap.fromList
                       [ Heap.Entry (c+c') (ch, a `fC` fE (v,ch,c',l))
                       | (ch,c',l) <- HashMap.lookupDefault [] v g
                       , not (ch `HashMap.member` visited)
                       ]
              in loop (Heap.union q' q2) (HashMap.insert v (c, a) visited)

-- ------------------------------------------------------------------------

-- | Floyd-Warshall algorithm for finding shortest paths in a weighted graph
-- with positive or negative edge weights (but with no negative cycles).
--
-- It compute shortest-paths between each pair of vertexes, and folds edge
-- information along shortest paths using a given 'Fold' operation.
floydWarshall
  :: forall vertex cost label a. (Eq vertex, Hashable vertex, Real cost)
  => Fold vertex cost label a
  -> HashMap vertex [OutEdge vertex cost label]
  -> HashMap (vertex,vertex) (cost, a)
floydWarshall (Fold fV fE fC) g = HashMap.unionWith minP (foldl' f tbl0 vs) paths0
  where
    vs = HashMap.keys g

    paths0 :: HashMap (vertex,vertex) (cost, a)
    paths0 = HashMap.fromList [((v,v), (0, fV v)) | v <- HashMap.keys g]

    tbl0 :: HashMap (vertex,vertex) (cost, a)
    tbl0 = HashMap.fromListWith minP [((v,u), (c, fE (v,u,c,l))) | (v, es) <- HashMap.toList g, (u,c,l) <- es]

    minP :: (cost, a) -> (cost, a) -> (cost, a)
    minP = minBy (comparing fst)

    f :: HashMap (vertex,vertex) (cost, a)
      -> vertex
      -> HashMap (vertex,vertex) (cost, a)
    f tbl vk = HashMap.unionWith minP tbl tbl'
      where
        tbl' = HashMap.fromList
          [ ((vi,vj), (c1+c2, fC a1 a2))
          | vi <- vs, (c1,a1) <- maybeToList (HashMap.lookup (vi,vk) tbl)
          , vj <- vs, (c2,a2) <- maybeToList (HashMap.lookup (vk,vj) tbl)
          ]

minBy :: (a -> a -> Ordering) -> a -> a -> a
minBy f a b =
  case f a b of
    LT -> a
    EQ -> a
    GT -> b

-- ------------------------------------------------------------------------
