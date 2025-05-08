{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Combinatorial.Knapsack.BB
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Simple 0-1 knapsack problem solver that uses branch-and-bound with LP-relaxation based upper bound.
--
-----------------------------------------------------------------------------
module ToySolver.Combinatorial.Knapsack.BB
  ( Weight
  , Value
  , solve
  ) where

import Control.Monad
import Control.Monad.State.Strict
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (sortOn)
import Data.Ord

type Weight = Rational
type Value  = Rational

solve
  :: [(Value, Weight)]
  -> Weight
  -> (Value, Weight, [Bool])
solve items limit =
  ( sum [v | (n,(v,_)) <- zip [0..] items, n `IntSet.member` sol]
  , sum [w | (n,(_,w)) <- zip [0..] items, n `IntSet.member` sol]
  , [n `IntSet.member` sol | (n,_) <- zip [0..] items]
  )
  where
    items' :: [(Value, Weight, Int)]
    items' = sortOn (\(v, w, _) -> Down ((v / w, v))) [(v, w, n) | (n, (v, w)) <- zip [0..] items, w > 0, v > 0]

    sol :: IntSet
    sol = IntSet.fromList [n | (n, (v, w)) <- zip [0..] items, w == 0, v > 0] `IntSet.union`
          IntSet.fromList (fst $ execState (f items' limit ([],0)) ([],0))

    f :: [(Value, Weight, Int)] -> Weight -> ([Int],Value) -> State ([Int],Value) ()
    f items !slack (is, !value) = do
      (_, bestVal) <- get
      when (computeUB items slack value > bestVal) $ do
        case items of
          [] -> put (is,value)
          (v,w,i):items -> do
            when (slack >= w) $ f items (slack - w) (i : is, v + value)
            -- Drop all indistingushable items for symmetry breaking
            f (dropWhile (\(v',w',_) -> v==v' && w==w') items) slack (is, value)

    computeUB :: [(Value, Weight, Int)] -> Weight -> Value -> Value
    computeUB items slack value = go items slack value
      where
        go _ 0 val  = val
        go [] _ val = val
        go ((v,w,_):items) slack val
          | slack >= w = go items (slack - w) (val + v)
          | otherwise   = val + (v / w) * slack
