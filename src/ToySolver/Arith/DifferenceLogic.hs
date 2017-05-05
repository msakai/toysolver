{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Arith.DifferenceLogic
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Reference:
--
-- * Albert Oliveras and Enric Rodriguez-Carbonell.
--   “General overview of a T-Solver for Difference Logic”.
--   <https://www.cs.upc.edu/~oliveras/TDV/dl.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.Arith.DifferenceLogic
  ( SimpleAtom
  , solve
  ) where

import Data.Hashable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet

import ToySolver.Graph.BellmanFord

-- (a,b,k) represents (a - b ≤ k)
type SimpleAtom v b = (v,v,b)

solve
  :: (Hashable label, Eq label, Hashable v, Eq v, Real b)
  => [(label, SimpleAtom v b)]
  -> Either (HashSet label) (HashMap v b)
solve xs =
  case bellmanford g vs of
    Left es -> Left $ HashSet.fromList [l | (_,l,_) <- es]
    Right m -> Right $ fmap (\(d, _) -> - d) m
  where
    vs = HashSet.toList $ HashSet.fromList [v | (_,(a,b,_)) <- xs, v <- [a,b]]
    g = HashMap.fromList [(a,[(b,k,l)]) | (l,(a,b,k)) <- xs]

-- M = {a−b ≤ 2, b−c ≤ 3, c−a ≤ −3}
test_sat = solve xs
  where
    xs :: [(Int, SimpleAtom Char Int)]
    xs = [(1, ('a','b',2)), (2, ('b','c',3)), (3, ('c','a',-3))]

-- M = {a−b ≤ 2, b−c ≤ 3, c−a ≤ −7}
test_unsat = solve xs
  where
    xs :: [(Int, SimpleAtom Char Int)]
    xs = [(1, ('a','b',2)), (2, ('b','c',3)), (3, ('c','a',-7))]
