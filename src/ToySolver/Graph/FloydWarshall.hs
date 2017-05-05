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
  , pathAppend
  , pathEdges
  , pathVertexes
  ) where

import Data.Hashable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.List (foldl')
import Data.Maybe

-- ------------------------------------------------------------------------

data Path vertex label cost 
  = Singleton vertex vertex label !cost
  | Append (Path vertex label cost) (Path vertex label cost) !cost
  deriving (Eq, Show)

pathFrom :: Path vertex label cost -> vertex
pathFrom (Singleton from _ _ _) = from
pathFrom (Append p1 _ _) = pathFrom p1

pathTo :: Path vertex label cost -> vertex
pathTo (Singleton _ to _ _) = to
pathTo (Append _ p2 _) = pathTo p2

pathCost :: Path vertex label cost -> cost
pathCost (Singleton _ _ _ c) = c
pathCost (Append _ _ c) = c

pathAppend :: Num cost => Path vertex label cost -> Path vertex label cost -> Path vertex label cost
pathAppend p1 p2 = Append p1 p2 (pathCost p1 + pathCost p2)

pathEdges :: Path vertex label cost -> [(vertex,vertex,label,cost)]
pathEdges p = f p []
  where
    f (Singleton v1 v2 l c) xs = (v1,v2,l,c) : xs
    f (Append p1 p2 _) xs = (f p1 . f p2) xs

pathVertexes :: Path vertex label cost -> [vertex]
pathVertexes p = f True p []
  where
    f True (Singleton v1 v2 _ _) xs = v1 : v2 : xs
    f False (Singleton v1 _ _ _) xs = v1 : xs
    f b (Append p1 p2 _) xs = (f False p1 . f b p2) xs

pathMin :: Ord cost => Path vertex label cost -> Path vertex label cost -> Path vertex label cost
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
