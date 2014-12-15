-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Knapsack.DP
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Simple 0-1 knapsack problem solver that uses DP.
--
-----------------------------------------------------------------------------
module ToySolver.Knapsack.DP
  ( Weight
  , Value
  , solve
  ) where

import Data.Array
import Data.Function (on)
import Data.List

type Weight = Int
type Value = Rational

solve
  :: [(Value, Weight)]
  -> Weight
  -> (Value, Weight, [Bool])
solve items limit = (val, sum [w | (b,(_,w)) <- zip bs items, b], bs)
  where
    bs = reverse bs'
    (bs',val) = m!(n-1, limit)

    n = length items
    m = array ((-1, 0), (n-1, limit)) $
          [((-1,w), ([],0)) | w <- [0 .. limit]] ++
          [((i,0), ([],0)) | i <- [0 .. n-1]] ++
          [((i,w), best) 
              | (i,(vi,wi)) <- zip [0..] items
              , w <- [1..limit]
              , let s1 = [(False:bs,v) | let (bs,v) = m!(i-1, w)]
              , let s2 = [(True:as,v+vi) | w >= wi, let (as,v) = m!(i-1, w-wi)]
              , let best = maximumBy (compare `on` snd) (s1 ++ s2)
          ]

test1 = solve [(5,4), (4,5), (3,2)] 9
test2 = solve [(45,5), (48,8), (35,3)] 10
