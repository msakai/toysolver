{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- ------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Graph.FloydWarshall
-- Copyright   :  (c) Masahiro Sakai 2017
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Floyd-Warshall algorithm for finding shortest paths in a weighted graph
-- with positive or negative edge weights (but with no negative cycles).
--
-- ------------------------------------------------------------------------
module ToySolver.Graph.FloydWarshall
  ( floydWarshall
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
  ) where

import Data.Hashable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.List (foldl')
import Data.Maybe
import Data.Monoid
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq

-- ------------------------------------------------------------------------

data Path vertex label cost 
  = Empty vertex
  | Singleton vertex vertex label !cost
  | Append (Path vertex label cost) (Path vertex label cost) !cost
  deriving (Eq, Show)

pathFrom :: Path vertex label cost -> vertex
pathFrom (Empty v) = v
pathFrom (Singleton from _ _ _) = from
pathFrom (Append p1 _ _) = pathFrom p1

pathTo :: Path vertex label cost -> vertex
pathTo (Empty v) = v
pathTo (Singleton _ to _ _) = to
pathTo (Append _ p2 _) = pathTo p2

pathCost :: Num cost => Path vertex label cost -> cost
pathCost (Empty _) = 0
pathCost (Singleton _ _ _ c) = c
pathCost (Append _ _ c) = c

pathEmpty :: vertex -> Path vertex label cost
pathEmpty = Empty

pathAppend :: (Eq vertex, Num cost) => Path vertex label cost -> Path vertex label cost -> Path vertex label cost
pathAppend p1 p2 
  | pathTo p1 /= pathFrom p2 = error "ToySolver.Graph.FloydWarshall.pathAppend: pathTo/pathFrom mismatch"
  | otherwise =
      case (p1, p2) of
        (Empty _, _) -> p2
        (_, Empty _) -> p1
        _ -> Append p1 p2 (pathCost p1 + pathCost p2)

pathEdges :: Path vertex label cost -> [(vertex,vertex,label,cost)]
pathEdges p = f p []
  where
    f (Empty _) xs = xs
    f (Singleton v1 v2 l c) xs = (v1,v2,l,c) : xs
    f (Append p1 p2 _) xs = f p1 (f p2 xs)

pathEdgesBackward :: Path vertex label cost -> [(vertex,vertex,label,cost)]
pathEdgesBackward p = f p []
  where
    f (Empty _) xs = xs
    f (Singleton v1 v2 l c) xs = (v1,v2,l,c) : xs
    f (Append p1 p2 _) xs = f p2 (f p1 xs)

pathEdgesSeq :: Path vertex label cost -> Seq (vertex,vertex,label,cost)
pathEdgesSeq (Empty _) = Seq.empty
pathEdgesSeq (Singleton v1 v2 l c) = Seq.singleton (v1,v2,l,c)
pathEdgesSeq (Append p1 p2 _) = pathEdgesSeq p1 <> pathEdgesSeq p2

pathVertexes :: Path vertex label cost -> [vertex]
pathVertexes p = pathFrom p : f p []
  where
    f (Empty _) xs = xs
    f (Singleton _ v2 _ _) xs = v2 : xs
    f (Append p1 p2 _) xs = f p1 (f p2 xs)

pathVertexesBackward :: Path vertex label cost -> [vertex]
pathVertexesBackward p = pathTo p : f p []
  where
    f (Empty _) xs = xs
    f (Singleton v1 _ _ _) xs = v1 : xs
    f (Append p1 p2 _) xs = f p2 (f p1 xs)

pathVertexesSeq :: Path vertex label cost -> Seq vertex
pathVertexesSeq p = f True p
  where
    f True  (Empty v) = Seq.singleton v
    f False (Empty _) = mempty
    f True  (Singleton v1 v2 _ _) = Seq.fromList [v1, v2]
    f False (Singleton v1 _ _ _)  = Seq.singleton v1
    f b (Append p1 p2 _) = f False p1 <> f b p2

pathMin :: (Num cost, Ord cost) => Path vertex label cost -> Path vertex label cost -> Path vertex label cost
pathMin p1 p2
  | pathCost p1 <= pathCost p2 = p1
  | otherwise = p2

-- ------------------------------------------------------------------------

floydWarshall
  :: forall vertex cost label. (Eq vertex, Hashable vertex, Real cost)
  => HashMap vertex [(vertex, cost, label)]
  -> HashMap (vertex,vertex) (Path vertex label cost)
floydWarshall g = foldl' f tbl0 vs
  where
    vs = HashMap.keys g

    tbl0 :: HashMap (vertex,vertex) (Path vertex label cost)
    tbl0 = HashMap.fromListWith pathMin [((v,u), Singleton v u l c) | (v, es) <- HashMap.toList g, (u,c,l) <- es]

    f :: HashMap (vertex,vertex) (Path vertex label cost)
      -> vertex
      -> HashMap (vertex,vertex) (Path vertex label cost)
    f tbl vk = HashMap.unionWith pathMin tbl tbl'
      where
        tbl' = HashMap.fromList
          [ ((vi,vj), pathAppend p1 p2)
          | vi <- vs, p1 <- maybeToList (HashMap.lookup (vi,vk) tbl)
          , vj <- vs, p2 <- maybeToList (HashMap.lookup (vk,vj) tbl)
          ]

-- ------------------------------------------------------------------------

-- https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm
exampleGraph :: HashMap Int [(Int, Rational, ())]
exampleGraph = HashMap.fromList
  [ (1, [(3,-2,())])
  , (2, [(1,4,()), (3,3,())])
  , (3, [(4,2,())])
  , (4, [(2,-1,())])
  ]
