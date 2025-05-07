{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Combinatorial.Knapsack.DPSparse
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Simple 0-1 knapsack problem solver that uses DP.
--
-----------------------------------------------------------------------------
module ToySolver.Combinatorial.Knapsack.DPSparse
  ( solve
  , solveInt
  , solveInteger
  , solveGeneric
  ) where

import Data.List (foldl', foldl1')
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

{-# RULES
"solve/Int"     solve = solveInt
"solve/Integer" solve = solveInteger
  #-}

solve
  :: forall value weight. (Real value, Real weight)
  => [(value, weight)]
  -> weight
  -> (value, weight, [Bool])
solve = solveGeneric

solveGeneric
  :: forall value weight. (Real value, Real weight)
  => [(value, weight)]
  -> weight
  -> (value, weight, [Bool])
solveGeneric items limit =
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

solveInt
  :: forall value. (Real value)
  => [(value, Int)]
  -> Int
  -> (value, Int, [Bool])
solveInt items limit =
  case IntMap.findMax table of
    (w, (v, sol)) -> (v, w, reverse sol)
  where
    table :: IntMap (value, [Bool])
    table = foldl' f empty items

    empty :: IntMap (value, [Bool])
    empty = IntMap.singleton 0 (0,[])

    f :: IntMap (value, [Bool]) -> (value, Int) -> IntMap (value, [Bool])
    f m (vi,wi)
      | wi < 0  = error "negative weight"
      | vi <= 0 = m0
      | wi == 0 = IntMap.map (\(v,sol) -> (v+vi, True : sol)) m
      | otherwise = removeDominated m2
      where
        m0 = IntMap.map (\(v,sol) -> (v, False : sol)) m
        m1 = splitLE limit $ IntMap.mapKeysMonotonic (+wi) $ IntMap.map (\(v,sol) -> (v+vi, True : sol)) $ m
        m2 = IntMap.unionWith (\a@(v1,_) b@(v2,_) -> if v1 < v2 then b else a) m0 m1

    removeDominated :: IntMap (value, [Bool]) -> IntMap (value, [Bool])
    removeDominated m = m2
      where
        m2 = IntMap.fromDistinctAscList . loop (-1) . IntMap.toAscList $ m
        loop _ [] = []
        loop !vmax (x@(_,(v1,_)) : xs)
          | vmax < v1 = x : loop v1 xs
          | otherwise = loop vmax xs

    splitLE :: Int -> IntMap v -> IntMap v
    splitLE k m
      | k == maxBound = m
      | otherwise =
          case IntMap.splitLookup (k+1) m of
            (lo, _, _) -> lo

solveInteger
  :: forall value. (Real value)
  => [(value, Integer)]
  -> Integer
  -> (value, Integer, [Bool])
solveInteger items limit
  | all (\(_,w) -> w <= maxInt) items' && limit' <= maxInt =
      case solveInt [(v, fromIntegral w) | (v,w) <- items'] (fromIntegral limit') of
        (v, w, sol) -> (v, fromIntegral w * d, sol)
  | otherwise =
      case solveGeneric items' limit' of
        (v, w, sol) -> (v, w * d, sol)
  where
    d = if null items then 1 else foldl1' gcd [w | (_v, w) <- items]
    items' = [(v, w `div` d) | (v, w) <- items]
    limit' = limit `div` d
    maxInt = fromIntegral (maxBound :: Int)
