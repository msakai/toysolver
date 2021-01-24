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
  ( SimpleAtom (..)
  , Var
  , Diff (..)
  , solve
  ) where

import Data.Hashable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Monoid

import ToySolver.Graph.ShortestPath (bellmanFord, lastInEdge, bellmanFordDetectNegativeCycle, monoid')

infixl 6 :-
infix 4 :<=

type Var = Int

-- | Difference of two variables
data Diff = Var :- Var
  deriving (Eq, Ord, Show)

-- | @a :- b :<= k@ represents /a - b ≤ k/
data SimpleAtom b = Diff :<= b
  deriving (Eq, Ord, Show)

-- | Takes labeled list of constraints, and returns eithera
--
-- * unsatisfiable set of constraints as a set of labels, or
--
-- * satisfying assignment.
solve
  :: (Hashable label, Eq label, Real b)
  => [(label, SimpleAtom b)]
  -> Either (HashSet label) (HashMap Var b)
solve xs =
  case bellmanFordDetectNegativeCycle (monoid' (\(_,_,_,l) -> Endo (l:))) g d of
    Just f -> Left $ HashSet.fromList $ appEndo f []
    Nothing -> Right $ fmap (\(c,_) -> - c) d
  where
    vs = HashSet.toList $ HashSet.fromList [v | (_,(a :- b :<= _)) <- xs, v <- [a,b]]
    g = HashMap.fromList [(a,[(b,k,l)]) | (l,(a :- b :<= k)) <- xs]
    d = bellmanFord lastInEdge g vs

-- M = {a−b ≤ 2, b−c ≤ 3, c−a ≤ −3}
_test_sat :: Either (HashSet Int) (HashMap Var Int)
_test_sat = solve xs
  where
    xs :: [(Int, SimpleAtom Int)]
    xs = [(1, (a :- b :<= 2)), (2, (b :- c :<= 3)), (3, (c :- a :<= -3))]
    [a,b,c] = [0..2]

-- M = {a−b ≤ 2, b−c ≤ 3, c−a ≤ −7}
_test_unsat :: Either (HashSet Int) (HashMap Var Int)
_test_unsat = solve xs
  where
    xs :: [(Int, SimpleAtom Int)]
    xs = [(1, (a :- b :<= 2)), (2, (b :- c :<= 3)), (3, (c :- a :<= -7))]
    [a,b,c] = [0..2]
