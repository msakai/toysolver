{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
--------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Graph.ShortestPath
-- Copyright   :  (c) Masahiro Sakai 2016-2017
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- This module provides functions for shotest path computation.
--
-- Reference:
--
-- * Friedrich Eisenbrand. “Linear and Discrete Optimization”.
--   <https://www.coursera.org/course/linearopt>
--
--------------------------------------------------------------------------
module ToySolver.Graph.ShortestPath
  (
  -- * Graph data types
    Graph
  , Edge
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
  , cost

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
  , pathMin

  -- * Shortest-path algorithms
  , bellmanFord
  , dijkstra
  , floydWarshall

  -- * Utility functions
  , bellmanFordDetectNegativeCycle
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
import qualified Data.HashSet as HashSet
import qualified Data.Heap as Heap -- http://hackage.haskell.org/package/heaps
import Data.List (foldl')
import Data.Monoid
import Data.Ord
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.STRef

-- ------------------------------------------------------------------------

-- | Graph represented as a map from vertexes to their outgoing edges
type Graph cost label = HashMap Vertex [OutEdge cost label]

-- | Vertex data type
type Vertex = Int

-- | Edge data type
type Edge cost label = (Vertex, Vertex, cost, label)

-- | Outgoing edge data type (source vertex is implicit)
type OutEdge cost label = (Vertex, cost, label)

-- | Incoming edge data type (target vertex is implicit)
type InEdge cost label = (Vertex, cost, label)

-- | path data type.
data Path cost label
  = Empty Vertex
    -- ^ empty path
  | Singleton (Edge cost label)
    -- ^ path with single edge
  | Append (Path cost label) (Path cost label) !cost
    -- ^ concatenation of two paths
  deriving (Eq, Show)

-- | Source vertex
pathFrom :: Path cost label -> Vertex
pathFrom (Empty v) = v
pathFrom (Singleton (from,_,_,_)) = from
pathFrom (Append p1 _ _) = pathFrom p1

-- | Target vertex
pathTo :: Path cost label -> Vertex
pathTo (Empty v) = v
pathTo (Singleton (_,to,_,_)) = to
pathTo (Append _ p2 _) = pathTo p2

-- | Cost of a path
pathCost :: Num cost => Path cost label -> cost
pathCost (Empty _) = 0
pathCost (Singleton (_,_,c,_)) = c
pathCost (Append _ _ c) = c

-- | Empty path
pathEmpty :: Vertex -> Path cost label
pathEmpty = Empty

-- | Concatenation of two paths
pathAppend :: (Num cost) => Path cost label -> Path cost label -> Path cost label
pathAppend p1 p2
  | pathTo p1 /= pathFrom p2 = error "ToySolver.Graph.ShortestPath.pathAppend: pathTo/pathFrom mismatch"
  | otherwise =
      case (p1, p2) of
        (Empty _, _) -> p2
        (_, Empty _) -> p1
        _ -> Append p1 p2 (pathCost p1 + pathCost p2)

-- | Edges of a path
pathEdges :: Path cost label -> [Edge cost label]
pathEdges p = f p []
  where
    f (Empty _) xs = xs
    f (Singleton e) xs = e : xs
    f (Append p1 p2 _) xs = f p1 (f p2 xs)

-- | Edges of a path, but in the reverse order
pathEdgesBackward :: Path cost label -> [Edge cost label]
pathEdgesBackward p = f p []
  where
    f (Empty _) xs = xs
    f (Singleton e) xs = e : xs
    f (Append p1 p2 _) xs = f p2 (f p1 xs)

-- | Edges of a path, but as `Seq`
pathEdgesSeq :: Path cost label -> Seq (Edge cost label)
pathEdgesSeq (Empty _) = Seq.empty
pathEdgesSeq (Singleton e) = Seq.singleton e
pathEdgesSeq (Append p1 p2 _) = pathEdgesSeq p1 <> pathEdgesSeq p2

-- | Vertexes of a path
pathVertexes :: Path cost label -> [Vertex]
pathVertexes p = pathFrom p : f p []
  where
    f (Empty _) xs = xs
    f (Singleton (_,v2,_,_)) xs = v2 : xs
    f (Append p1 p2 _) xs = f p1 (f p2 xs)

-- | Vertexes of a path, but in the reverse order
pathVertexesBackward :: Path cost label -> [Vertex]
pathVertexesBackward p = pathTo p : f p []
  where
    f (Empty _) xs = xs
    f (Singleton (v1,_,_,_)) xs = v1 : xs
    f (Append p1 p2 _) xs = f p2 (f p1 xs)

-- | Vertex of a path, but as `Seq`
pathVertexesSeq :: Path cost label -> Seq Vertex
pathVertexesSeq p = f True p
  where
    f True  (Empty v) = Seq.singleton v
    f False (Empty _) = mempty
    f True  (Singleton (v1,v2,_,_)) = Seq.fromList [v1, v2]
    f False (Singleton (v1,_,_,_))  = Seq.singleton v1
    f b (Append p1 p2 _) = f False p1 <> f b p2

pathMin :: (Num cost, Ord cost) => Path cost label -> Path cost label -> Path cost label
pathMin p1 p2
  | pathCost p1 <= pathCost p2 = p1
  | otherwise = p2

-- | Fold a path using a given 'Fold` operation.
pathFold :: Fold cost label a -> Path cost label -> a
pathFold (Fold fV fE fC fD) p = fD (h p)
  where
    h (Empty v) = fV v
    h (Singleton e) = fE e
    h (Append p1 p2 _) = fC (h p1) (h p2)

-- ------------------------------------------------------------------------

-- | Strict pair type
data Pair a b = Pair !a !b

-- ------------------------------------------------------------------------

-- | Operations for folding edge information along with a path into a @r@ value.
--
-- @Fold cost label r@ consists of three operations
--
-- * @Vertex -> a@ corresponds to an empty path,
--
-- * @Edge cost label -> a@ corresponds to a single edge,
--
-- * @a -> a -> a@ corresponds to path concatenation,
--
-- and @a -> r@ to finish the computation.
data Fold cost label r
  = forall a. Fold (Vertex -> a) (Edge cost label -> a) (a -> a -> a) (a -> r)

instance Functor (Fold cost label) where
  {-# INLINE fmap #-}
  fmap f (Fold fV fE fC fD) = Fold fV fE fC (f . fD)

instance Applicative (Fold cost label) where
  {-# INLINE pure #-}
  pure a = Fold (\_ -> ()) (\_ -> ()) (\_ _ -> ()) (const a)

  {-# INLINE (<*>) #-}
  Fold fV1 fE1 fC1 fD1 <*> Fold fV2 fE2 fC2 fD2 =
    Fold (\v -> Pair (fV1 v) (fV2 v))
         (\e -> Pair (fE1 e) (fE2 e))
         (\(Pair a1 b1) (Pair a2 b2) -> Pair (fC1 a1 a2) (fC2 b1 b2))
         (\(Pair a b) -> fD1 a (fD2 b))

-- | Project `Edge` into a monoid value and fold using monoidal operation.
monoid' :: Monoid m => (Edge cost label -> m) -> Fold cost label m
monoid' f = Fold (\_ -> mempty) f mappend id

-- | Similar to 'monoid'' but a /label/ is directly used as a monoid value.
monoid :: Monoid m => Fold cost m m
monoid = monoid' (\(_,_,_,m) -> m)

-- | Ignore contents and return a unit value.
unit :: Fold cost label ()
unit = monoid' (\_ -> ())

-- | Pairs two `Fold` into one that produce a tuple.
pair :: Fold cost label a -> Fold cost label b -> Fold cost label (a,b)
pair (Fold fV1 fE1 fC1 fD1) (Fold fV2 fE2 fC2 fD2) =
  Fold (\v -> Pair (fV1 v) (fV2 v))
       (\e -> Pair (fE1 e) (fE2 e))
       (\(Pair a1 b1) (Pair a2 b2) -> Pair (fC1 a1 a2) (fC2 b1 b2))
       (\(Pair a b) -> (fD1 a, fD2 b))

-- | Construct a `Path` value.
path :: (Num cost) => Fold cost label (Path cost label)
path = Fold pathEmpty Singleton pathAppend id

-- | Compute cost of a path.
cost :: Num cost => Fold cost label cost
cost = Fold (\_ -> 0) (\(_,_,c,_) -> c) (+) id

-- | Get the first `OutEdge` of a path.
firstOutEdge :: Fold cost label (First (OutEdge cost label))
firstOutEdge = monoid' (\(_,v,c,l) -> First (Just (v,c,l)))

-- | Get the last `InEdge` of a path.
-- This is useful for constructing a /parent/ map of a spanning tree.
lastInEdge :: Fold cost label (Last (InEdge cost label))
lastInEdge = monoid' (\(v,_,c,l) -> Last (Just (v,c,l)))

-- ------------------------------------------------------------------------

-- | Bellman-Ford algorithm for finding shortest paths from source vertexes
-- to all of the other vertices in a weighted graph with negative weight
-- edges allowed.
--
-- It compute shortest-paths from given source vertexes, and folds edge
-- information along shortest paths using a given 'Fold' operation.
bellmanFord
  :: Real cost
  => Fold cost label a
     -- ^ Operation used to fold shotest paths
  -> Graph cost label
  -> [Vertex]
     -- ^ List of source vertexes @vs@
  -> HashMap Vertex (cost, a)
bellmanFord (Fold fV fE fC fD) g ss = runST $ do
  let n = HashMap.size g
  d <- C.newSized n
  forM_ ss $ \s -> H.insert d s (Pair 0 (fV s))

  updatedRef <- newSTRef (HashSet.fromList ss)
  _ <- runExceptT $ replicateM_ n $ do
    us <- lift $ readSTRef updatedRef
    when (HashSet.null us) $ throwE ()
    lift $ do
      writeSTRef updatedRef HashSet.empty
      forM_ (HashSet.toList us) $ \u -> do
        -- modifySTRef' updatedRef (HashSet.delete u) -- possible optimization
        Just (Pair du a) <- H.lookup d u
        forM_ (HashMap.lookupDefault [] u g) $ \(v, c, l) -> do
          m <- H.lookup d v
          case m of
            Just (Pair c0 _) | c0 <= du + c -> return ()
            _ -> do
              H.insert d v (Pair (du + c) (a `fC` fE (u,v,c,l)))
              modifySTRef' updatedRef (HashSet.insert v)

  liftM (fmap (\(Pair c x) -> (c, fD x))) $ freezeHashTable d

freezeHashTable :: (H.HashTable h, Hashable k, Eq k) => h s k v -> ST s (HashMap k v)
freezeHashTable h = H.foldM (\m (k,v) -> return $! HashMap.insert k v m) HashMap.empty h

-- | Utility function for detecting a negative cycle.
bellmanFordDetectNegativeCycle
  :: forall cost label a. Real cost
  => Fold cost label a
     -- ^ Operation used to fold a cycle
  -> Graph cost label
  -> HashMap Vertex (cost, Last (InEdge cost label))
     -- ^ Result of @'bellmanFord' 'lastInEdge' vs@
  -> Maybe a
bellmanFordDetectNegativeCycle (Fold fV fE fC fD) g d = either (Just . fD) (const Nothing) $ do
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
  :: forall cost label a. Real cost
  => Fold cost label a
     -- ^ Operation used to fold shotest paths
  -> Graph cost label
  -> [Vertex]
     -- ^ List of source vertexes
  -> HashMap Vertex (cost, a)
dijkstra (Fold fV fE fC (fD :: x -> a)) g ss =
  fmap (\(Pair c x) -> (c, fD x)) $
    loop (Heap.fromList [Heap.Entry 0 (Pair s (fV s)) | s <- ss]) HashMap.empty
  where
    loop
      :: Heap.Heap (Heap.Entry cost (Pair Vertex x))
      -> HashMap Vertex (Pair cost x)
      -> HashMap Vertex (Pair cost x)
    loop q visited =
      case Heap.viewMin q of
        Nothing -> visited
        Just (Heap.Entry c (Pair v a), q')
          | v `HashMap.member` visited -> loop q' visited
          | otherwise ->
              let q2 = Heap.fromList
                       [ Heap.Entry (c+c') (Pair ch (a `fC` fE (v,ch,c',l)))
                       | (ch,c',l) <- HashMap.lookupDefault [] v g
                       , not (ch `HashMap.member` visited)
                       ]
              in loop (Heap.union q' q2) (HashMap.insert v (Pair c a) visited)

-- ------------------------------------------------------------------------

-- | Floyd-Warshall algorithm for finding shortest paths in a weighted graph
-- with positive or negative edge weights (but with no negative cycles).
--
-- It compute shortest-paths between each pair of vertexes, and folds edge
-- information along shortest paths using a given 'Fold' operation.
floydWarshall
  :: forall cost label a. Real cost
  => Fold cost label a
     -- ^ Operation used to fold shotest paths
  -> Graph cost label
  -> HashMap Vertex (HashMap Vertex (cost, a))
floydWarshall (Fold fV fE fC (fD :: x -> a)) g =
  fmap (fmap (\(Pair c x) -> (c, fD x))) $
    HashMap.unionWith (HashMap.unionWith minP) (foldl' f tbl0 vs) paths0
  where
    vs = HashMap.keys g

    paths0 :: HashMap Vertex (HashMap Vertex (Pair cost x))
    paths0 = HashMap.mapWithKey (\v _ -> HashMap.singleton v (Pair 0 (fV v))) g

    tbl0 :: HashMap Vertex (HashMap Vertex (Pair cost x))
    tbl0 = HashMap.mapWithKey (\v es -> HashMap.fromListWith minP [(u, (Pair c (fE (v,u,c,l)))) | (u,c,l) <- es]) g

    minP :: Pair cost x -> Pair cost x -> Pair cost x
    minP = minBy (comparing (\(Pair c _) -> c))

    f :: HashMap Vertex (HashMap Vertex (Pair cost x))
      -> Vertex
      -> HashMap Vertex (HashMap Vertex (Pair cost x))
    f tbl vk =
      case HashMap.lookup vk tbl of
        Nothing -> tbl
        Just hk -> HashMap.map h tbl
          where
            h :: HashMap Vertex (Pair cost x) -> HashMap Vertex (Pair cost x)
            h m =
              case HashMap.lookup vk m of
                Nothing -> m
                Just (Pair c1 x1) -> HashMap.unionWith minP m (HashMap.map (\(Pair c2 x2) -> (Pair (c1+c2) (fC x1 x2))) hk)

minBy :: (a -> a -> Ordering) -> a -> a -> a
minBy f a b =
  case f a b of
    LT -> a
    EQ -> a
    GT -> b

-- ------------------------------------------------------------------------
