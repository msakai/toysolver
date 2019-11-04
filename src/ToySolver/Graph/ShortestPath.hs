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
type Graph vertex cost label = HashMap vertex [OutEdge vertex cost label]

-- | Edge data type
type Edge vertex cost label = (vertex, vertex, cost, label)

-- | Outgoing edge data type (source vertex is implicit)
type OutEdge vertex cost label = (vertex, cost, label)

-- | Incoming edge data type (target vertex is implicit)
type InEdge vertex cost label = (vertex, cost, label)

-- | path data type.
data Path vertex cost label
  = Empty vertex
    -- ^ empty path
  | Singleton (Edge vertex cost label)
    -- ^ path with single edge
  | Append (Path vertex cost label) (Path vertex cost label) !cost
    -- ^ concatenation of two paths
  deriving (Eq, Show)

-- | Source vertex
pathFrom :: Path vertex cost label -> vertex
pathFrom (Empty v) = v
pathFrom (Singleton (from,_,_,_)) = from
pathFrom (Append p1 _ _) = pathFrom p1

-- | Target vertex
pathTo :: Path vertex cost label -> vertex
pathTo (Empty v) = v
pathTo (Singleton (_,to,_,_)) = to
pathTo (Append _ p2 _) = pathTo p2

-- | Cost of a path
pathCost :: Num cost => Path vertex cost label -> cost
pathCost (Empty _) = 0
pathCost (Singleton (_,_,c,_)) = c
pathCost (Append _ _ c) = c

-- | Empty path
pathEmpty :: vertex -> Path vertex cost label
pathEmpty = Empty

-- | Concatenation of two paths
pathAppend :: (Eq vertex, Num cost) => Path vertex cost label -> Path vertex cost label -> Path vertex cost label
pathAppend p1 p2
  | pathTo p1 /= pathFrom p2 = error "ToySolver.Graph.ShortestPath.pathAppend: pathTo/pathFrom mismatch"
  | otherwise =
      case (p1, p2) of
        (Empty _, _) -> p2
        (_, Empty _) -> p1
        _ -> Append p1 p2 (pathCost p1 + pathCost p2)

-- | Edges of a path
pathEdges :: Path vertex cost label -> [Edge vertex cost label]
pathEdges p = f p []
  where
    f (Empty _) xs = xs
    f (Singleton e) xs = e : xs
    f (Append p1 p2 _) xs = f p1 (f p2 xs)

-- | Edges of a path, but in the reverse order
pathEdgesBackward :: Path vertex cost label -> [Edge vertex cost label]
pathEdgesBackward p = f p []
  where
    f (Empty _) xs = xs
    f (Singleton e) xs = e : xs
    f (Append p1 p2 _) xs = f p2 (f p1 xs)

-- | Edges of a path, but as `Seq`
pathEdgesSeq :: Path vertex cost label -> Seq (Edge vertex cost label)
pathEdgesSeq (Empty _) = Seq.empty
pathEdgesSeq (Singleton e) = Seq.singleton e
pathEdgesSeq (Append p1 p2 _) = pathEdgesSeq p1 <> pathEdgesSeq p2

-- | Vertexes of a path
pathVertexes :: Path vertex cost label -> [vertex]
pathVertexes p = pathFrom p : f p []
  where
    f (Empty _) xs = xs
    f (Singleton (_,v2,_,_)) xs = v2 : xs
    f (Append p1 p2 _) xs = f p1 (f p2 xs)

-- | Vertexes of a path, but in the reverse order
pathVertexesBackward :: Path vertex cost label -> [vertex]
pathVertexesBackward p = pathTo p : f p []
  where
    f (Empty _) xs = xs
    f (Singleton (v1,_,_,_)) xs = v1 : xs
    f (Append p1 p2 _) xs = f p2 (f p1 xs)

-- | Vertex of a path, but as `Seq`
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

-- | Fold a path using a given 'Fold` operation.
pathFold :: Fold vertex cost label a -> Path vertex cost label -> a
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
-- @Fold vertex cost label r@ consists of three operations
--
-- * @vertex -> a@ corresponds to an empty path,
--
-- * @Edge vertex cost label -> a@ corresponds to a single edge,
--
-- * @a -> a -> a@ corresponds to path concatenation,
--
-- and @a -> r@ to finish the computation.
data Fold vertex cost label r
  = forall a. Fold (vertex -> a) (Edge vertex cost label -> a) (a -> a -> a) (a -> r)

instance Functor (Fold vertex cost label) where
  {-# INLINE fmap #-}
  fmap f (Fold fV fE fC fD) = Fold fV fE fC (f . fD)

instance Applicative (Fold vertex cost label) where
  {-# INLINE pure #-}
  pure a = Fold (\_ -> ()) (\_ -> ()) (\_ _ -> ()) (const a)

  {-# INLINE (<*>) #-}
  Fold fV1 fE1 fC1 fD1 <*> Fold fV2 fE2 fC2 fD2 =
    Fold (\v -> Pair (fV1 v) (fV2 v))
         (\e -> Pair (fE1 e) (fE2 e))
         (\(Pair a1 b1) (Pair a2 b2) -> Pair (fC1 a1 a2) (fC2 b1 b2))
         (\(Pair a b) -> fD1 a (fD2 b))

-- | Project `Edge` into a monoid value and fold using monoidal operation.
monoid' :: Monoid m => (Edge vertex cost label -> m) -> Fold vertex cost label m
monoid' f = Fold (\_ -> mempty) f mappend id

-- | Similar to 'monoid'' but a /label/ is directly used as a monoid value.
monoid :: Monoid m => Fold vertex cost m m
monoid = monoid' (\(_,_,_,m) -> m)

-- | Ignore contents and return a unit value.
unit :: Fold vertex cost label ()
unit = monoid' (\_ -> ())

-- | Pairs two `Fold` into one that produce a tuple.
pair :: Fold vertex cost label a -> Fold vertex cost label b -> Fold vertex cost label (a,b)
pair (Fold fV1 fE1 fC1 fD1) (Fold fV2 fE2 fC2 fD2) =
  Fold (\v -> Pair (fV1 v) (fV2 v))
       (\e -> Pair (fE1 e) (fE2 e))
       (\(Pair a1 b1) (Pair a2 b2) -> Pair (fC1 a1 a2) (fC2 b1 b2))
       (\(Pair a b) -> (fD1 a, fD2 b))

-- | Construct a `Path` value.
path :: (Eq vertex, Num cost) => Fold vertex cost label (Path vertex cost label)
path = Fold pathEmpty Singleton pathAppend id

-- | Compute cost of a path.
cost :: Num cost => Fold vertex cost label cost
cost = Fold (\_ -> 0) (\(_,_,c,_) -> c) (+) id

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
bellmanFord
  :: (Eq vertex, Hashable vertex, Real cost)
  => Fold vertex cost label a
     -- ^ Operation used to fold shotest paths
  -> Graph vertex cost label
  -> [vertex]
     -- ^ List of source vertexes @vs@
  -> HashMap vertex (cost, a)
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
  :: forall vertex cost label a. (Eq vertex, Hashable vertex, Real cost)
  => Fold vertex cost label a
     -- ^ Operation used to fold a cycle
  -> Graph vertex cost label
  -> HashMap vertex (cost, Last (InEdge vertex cost label))
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
  :: forall vertex cost label a. (Eq vertex, Hashable vertex, Real cost)
  => Fold vertex cost label a
     -- ^ Operation used to fold shotest paths
  -> Graph vertex cost label
  -> [vertex]
     -- ^ List of source vertexes
  -> HashMap vertex (cost, a)
dijkstra (Fold fV fE fC (fD :: x -> a)) g ss =
  fmap (\(Pair c x) -> (c, fD x)) $
    loop (Heap.fromList [Heap.Entry 0 (Pair s (fV s)) | s <- ss]) HashMap.empty
  where
    loop
      :: Heap.Heap (Heap.Entry cost (Pair vertex x))
      -> HashMap vertex (Pair cost x)
      -> HashMap vertex (Pair cost x)
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
  :: forall vertex cost label a. (Eq vertex, Hashable vertex, Real cost)
  => Fold vertex cost label a
     -- ^ Operation used to fold shotest paths
  -> Graph vertex cost label
  -> HashMap vertex (HashMap vertex (cost, a))
floydWarshall (Fold fV fE fC (fD :: x -> a)) g =
  fmap (fmap (\(Pair c x) -> (c, fD x))) $
    HashMap.unionWith (HashMap.unionWith minP) (foldl' f tbl0 vs) paths0
  where
    vs = HashMap.keys g

    paths0 :: HashMap vertex (HashMap vertex (Pair cost x))
    paths0 = HashMap.mapWithKey (\v _ -> HashMap.singleton v (Pair 0 (fV v))) g

    tbl0 :: HashMap vertex (HashMap vertex (Pair cost x))
    tbl0 = HashMap.mapWithKey (\v es -> HashMap.fromListWith minP [(u, (Pair c (fE (v,u,c,l)))) | (u,c,l) <- es]) g

    minP :: Pair cost x -> Pair cost x -> Pair cost x
    minP = minBy (comparing (\(Pair c _) -> c))

    f :: HashMap vertex (HashMap vertex (Pair cost x))
      -> vertex
      -> HashMap vertex (HashMap vertex (Pair cost x))
    f tbl vk =
      case HashMap.lookup vk tbl of
        Nothing -> tbl
        Just hk -> HashMap.map h tbl
          where
            h :: HashMap vertex (Pair cost x) -> HashMap vertex (Pair cost x)
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
