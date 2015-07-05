{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Combinatorial.Knapsack.DP2
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables)
--
-- Simple 0-1 knapsack problem solver that uses DP.
--
-----------------------------------------------------------------------------
module ToySolver.Combinatorial.Knapsack.DP2
  ( solve
  ) where

import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

solve
  :: forall value weight. (Real value, Real weight)
  => [(value, weight)]
  -> weight
  -> (value, weight, [Bool])
solve items limit =
  case Map.findMax table of
    (w, (v, sol)) -> (v, w, reverse sol)
  where
    table :: Map weight (value, [Bool])
    table = foldl' f empty items

    empty :: Map weight (value, [Bool])
    empty = Map.singleton 0 (0,[])

    f :: Map weight (value, [Bool]) -> (value, weight) -> Map weight (value, [Bool])
    f m (vi,wi)
      | wi < 0  = error "negative weight"
      | vi <= 0 = m0
      | wi == 0 = Map.map (\(v,sol) -> (v+vi, True : sol)) m
      | otherwise = removeDominated m2
      where
        m0 = Map.map (\(v,sol) -> (v, False : sol)) m
        m1 = splitLE limit $ Map.mapKeysMonotonic (+wi) $ Map.map (\(v,sol) -> (v+vi, True : sol)) $ m
        m2 = Map.unionWith (\a@(v1,_) b@(v2,_) -> if v1 < v2 then b else a) m0 m1

    removeDominated :: Map weight (value, [Bool]) -> Map weight (value, [Bool])
    removeDominated m = m2
      where
        m2 = Map.fromDistinctAscList . loop (-1) . Map.toAscList $ m
        loop _ [] = []
        loop !vmax (x@(_,(v1,_)) : xs)
          | vmax < v1 = x : loop v1 xs
          | otherwise = loop vmax xs

splitLE :: Ord k => k -> Map k v -> Map k v
splitLE k m =
  case Map.splitLookup k m of
    (lo, Nothing, _) -> lo
    (lo, Just v, _) -> Map.insert k v lo

test1 = solve [(5,4), (4,5), (3,2)] 9
test2 = solve [(45,5), (48,8), (35,3)] 10
