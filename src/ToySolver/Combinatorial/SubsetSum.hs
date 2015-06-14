{-# LANGUAGE ScopedTypeVariables, BangPatterns, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Combinatorial.SubsetSum
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, BangPatterns, FlexibleContexts)
--
-- References
--
-- * D. Pisinger, "An exact algorithm for large multiple knapsack problems,"
--   European Journal of Operational Research, vol. 114, no. 3, pp. 528-541,
--   May 1999. DOI:10.1016/s0377-2217(98)00120-9
--   <http://www.sciencedirect.com/science/article/pii/S0377221798001209>
--   <http://www.diku.dk/~pisinger/95-6.ps>
--
-----------------------------------------------------------------------------
module ToySolver.Combinatorial.SubsetSum
  ( Weight
  , solve
  ) where

import Control.Exception (assert)
import Control.Loop -- loop package
import Control.Monad
import Control.Monad.ST
import Data.STRef
import Data.Array.ST
import Data.Vector.Generic ((!))
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import qualified Data.Vector.Unboxed as VU

type Weight = Int

-- | Maximize Σ_{i=1}^n wi xi subject to Σ_{i=1}^n wi xi ≤ c and xi ∈ {0,1}.
--
-- Note: 0 (resp. 1) is identified with False (resp. True) in the assignment.
solve
  :: V.Vector v Weight
  => v Weight -- ^ weights @[w1, w2 .. wn]@
  -> Weight -- ^ capacity @c@
  -> (Weight, VU.Vector Bool)
  -- ^
  -- * the objective value Σ_{i=1}^n wi xi, and
  --
  -- * the assignment @[x1, x2 .. xn]@, identifying 0 (resp. 1) with @False@ (resp. @True@).
solve w c
  | c < 0 = error $ "SubsetSum.solve: capacity " ++ show c ++ " should be non-negative"
  | Just x <- V.find (<0) w = error $ "ToySolver.Combinatorial.SubsetSum.solve: weight " ++ show x ++ " should be non-negative"
  | Just _ <- V.find (>c) w =
      let (obj,bs) = solve' (V.filter (<=c) w) c
          bs2 = VU.create $ do
            v <- VM.new (V.length w)
            let loop !i !j =
                  when (i < V.length w) $ do
                    if w ! i <= c then do
                      VM.write v i (bs ! j)
                      loop (i+1) (j+1)
                    else do
                      VM.write v i False
                      loop (i+1) j
            loop 0 0
            return v
      in (obj, bs2)
  | otherwise = solve' w c

solve' :: V.Vector v Weight => v Weight -> Weight -> (Weight, VU.Vector Bool)
solve' w !c
  | wsum <= fromIntegral c = (fromIntegral wsum, V.replicate n True)
  | otherwise = assert (wbar <= c) $ assert (wbar + (w ! b) > c) $ runST m
  where
    n = V.length w

    b :: Int
    b = loop (-1) 0
      where
        loop :: Int -> Integer -> Int
        loop !i !s
          | s > fromIntegral c = i
          | otherwise = loop (i+1) (s + fromIntegral (w ! (i+1)))

    -- Integer is used to avoid integer overflow
    wsum :: Integer
    wsum = V.foldl' (\r x -> r + fromIntegral x) 0 w

    wbar :: Weight
    -- wbar = sum [wA ! j | j <- [0..b-1]]
    wbar = loop 0 0
      where
        loop !j !ret
          | j == b = ret
          | otherwise = loop (j+1) (ret + (w ! j))

    v :: Integer
    v = wsum - fromIntegral wbar

    f_range :: (Weight, Weight)
    f_range = if v < fromIntegral c then (0, fromIntegral v) else (0, c)

    g_range :: (Weight, Weight)
    g_range = if v < fromIntegral c then (c - fromIntegral v, c) else (0, c)

    m :: forall s. ST s (Weight, VU.Vector Bool)
    m = do
      (f_buff :: STUArray s Weight Weight) <- newArray_ f_range
      (g_buff :: STUArray s Weight Weight) <- newArray_ g_range
      (f_hist :: STUArray s Weight Int) <- newArray f_range (-1)
      (g_hist :: STUArray s Weight Int) <- newArray g_range (-1)

      -- Initialize f_buff with f_{b-1}
      forM_ (range f_range) $ \c' -> writeArray f_buff c' 0

      -- Initialize g_buff with g_b
      forM_ (range g_range) $ \c' ->
        if c' >= wbar then 
          writeArray g_buff c' wbar
        else
          writeArray g_buff c' (-1) -- INFEASIBLE

      let -- Given f_{t-1} in f_buff and t, compute f_t and update f_buff with it.
          update_ft !t = do
            let wt = w ! t
            forLoop (snd f_range) (>= fst f_range) (subtract 1) $ \c' -> do
              when (c' >= wt) $ do
                obj1 <- readArray f_buff c'
                obj2 <- readArray f_buff (c' - wt)
                when (obj1 < obj2 + wt) $ do
                  writeArray f_buff c' (obj2 + wt)
                  writeArray f_hist c' t

          -- Given g_{s+1} in g_buff and s, compute g_s and update g_buff with it.
          update_gs !s = do
            let ws = w ! s
            forLoop (fst g_range) (<= snd g_range) (+1) $ \c' -> do
              when (c' + ws <= c) $ do
                obj1 <- readArray g_buff c'
                obj2 <- readArray g_buff (c' + ws)
                when (obj1 < 0 || obj1 < obj2 - ws) $ do
                  writeArray g_buff c' (max (-1) (obj2 - ws))
                  writeArray g_hist c' s

          build :: Int -> ST s (VU.Vector Bool)
          build !c' = do
            bs <- VM.new n
            forM_ [0..b-1] $ \i -> VM.write bs i True
            forM_ [b..n-1] $ \i -> VM.write bs i False
            let rem_loop !c'' = do
                  i <- readArray g_hist c''
                  unless (i == -1) $ do
                    VM.write bs i False
                    rem_loop (c'' + (w ! i))
            let add_loop !c'' = do
                  i <- readArray f_hist c''
                  unless (i == -1) $ do
                    VM.write bs i True
                    add_loop (c'' - (w ! i))
            rem_loop (c - c')
            add_loop c'
            V.unsafeFreeze bs

      zRef <- newSTRef (-1)
      cRef <- newSTRef (-1)
      let compute_best = do
            writeSTRef zRef (-1)
            writeSTRef cRef (-1)
            forM_ (range f_range) $ \c' -> do
              obj_g <- readArray g_buff (c - c')
              when (obj_g >= 0) $ do
                obj_f <- readArray f_buff c'
                let obj = obj_f + obj_g
                obj_curr <- readSTRef zRef
                when (obj > obj_curr) $ do
                  writeSTRef zRef obj
                  writeSTRef cRef c'
            z <- readSTRef zRef
            c' <- readSTRef cRef
            return (z,c')      

      let loop !s !t !flag = do
            (obj, c') <- compute_best
            if obj == c || (s == 0 && t == n-1) then do
              bs <- build c'
              return (obj, bs)
            else do
              let m1 = update_gs (s-1) >> loop (s-1) t (not flag)
                  m2 = update_ft (t+1) >> loop s (t+1) (not flag)
              if s /= 0 && t /= n-1 then
                if flag then m1 else m2
              else if s /= 0 then
                m1
              else -- t /= n-1
                m2
      loop b (b-1) True
