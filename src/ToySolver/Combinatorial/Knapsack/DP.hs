{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Combinatorial.Knapsack.DP
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables)
--
-- Simple 0-1 knapsack problem solver that uses DP.
--
-----------------------------------------------------------------------------
module ToySolver.Combinatorial.Knapsack.DP
  ( Weight
  , Value
  , solve
  ) where

import Control.Exception (assert)
import Control.Loop
import Control.Monad
import Control.Monad.ST
import Data.Array.ST
import Data.Function (on)
import Data.List

type Weight = Int
type Value = Rational

solve
  :: [(Value, Weight)]
  -> Weight
  -> (Value, Weight, [Bool])
solve items limit = runST m
  where
    m :: forall s. ST s (Value, Weight, [Bool])
    m = do
      (table :: STArray s Weight (Value, Weight, [Bool])) <- newArray (0, limit)  (0,0,[])
      forM_ items $ \(v,w) -> do
        forLoop limit (>=0) (subtract 1) $ \c -> do
          assert (w >= 0) $ return ()
          if w <= c then do
            (obj1, w1, sol1) <- readArray table c
            (obj2, w2, sol2) <- readArray table (c - w)
            seq w1 $ seq w2 $ return () -- XXX
            if v >= 0 && obj2 + v > obj1 then do
              writeArray table c (obj2 + v, w2 + w, True : sol2)
            else
              writeArray table c (obj1, w1, False : sol1)
          else do
            (obj1, w1, sol1) <- readArray table c
            writeArray table c (obj1, w1, False : sol1)
      (obj, w, sol) <- readArray table limit
      return (obj, w, reverse sol)

test1 = solve [(5,4), (4,5), (3,2)] 9
test2 = solve [(45,5), (48,8), (35,3)] 10
