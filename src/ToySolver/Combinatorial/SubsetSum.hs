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
  , subsetSum
  , maxSubsetSum
  , minSubsetSum
  ) where

import Control.Exception (assert)
import Control.Loop -- loop package
import Control.Monad
import Control.Monad.ST
import Data.STRef
import Data.Array.ST
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Vector.Generic ((!))
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import qualified Data.Vector.Unboxed as VU

type Weight = Int

-- | Maximize Σ_{i=1}^n wi xi subject to Σ_{i=1}^n wi xi ≤ c and xi ∈ {0,1}.
--
-- Note: 0 (resp. 1) is identified with False (resp. True) in the assignment.
maxSubsetSum
  :: V.Vector v Weight
  => v Weight -- ^ weights @[w1, w2 .. wn]@
  -> Weight -- ^ capacity @c@
  -> (Weight, VU.Vector Bool)
  -- ^
  -- * the objective value Σ_{i=1}^n wi xi, and
  --
  -- * the assignment @[x1, x2 .. xn]@, identifying 0 (resp. 1) with @False@ (resp. @True@).
maxSubsetSum w c
  | c < 0 = error $ "SubsetSum.maxSubsetSum: capacity " ++ show c ++ " should be non-negative"
  | Just x <- V.find (<0) w = error $ "ToySolver.Combinatorial.SubsetSum.maxSubsetSum: weight " ++ show x ++ " should be non-negative"
  | Just _ <- V.find (>c) w =
      let (obj,bs) = maxSubsetSum' (V.filter (<=c) w) c
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
  | otherwise = maxSubsetSum' w c

maxSubsetSum' :: V.Vector v Weight => v Weight -> Weight -> (Weight, VU.Vector Bool)
maxSubsetSum' w !c
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
      (f_hist :: STArray s Weight [Int]) <- newArray f_range []
      (g_hist :: STArray s Weight [Int]) <- newArray g_range []

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
                  hist2 <- readArray f_hist (c' - wt)
                  writeArray f_buff c' (obj2 + wt)
                  writeArray f_hist c' (t : hist2)

          -- Given g_{s+1} in g_buff and s, compute g_s and update g_buff with it.
          update_gs !s = do
            let ws = w ! s
            forLoop (fst g_range) (<= snd g_range) (+1) $ \c' -> do
              when (c' + ws <= c) $ do
                obj1 <- readArray g_buff c'
                obj2 <- readArray g_buff (c' + ws)
                when (obj1 < 0 || obj1 < obj2 - ws) $ do
                  hist2 <- readArray g_hist (c' + ws)
                  writeArray g_buff c' (max (-1) (obj2 - ws))
                  writeArray g_hist c' (s : hist2)

          build :: Int -> ST s (VU.Vector Bool)
          build !c' = do
            bs <- VM.new n
            forM_ [0..b-1] $ \i -> VM.write bs i True
            forM_ [b..n-1] $ \i -> VM.write bs i False
            added <- readArray f_hist c'
            removed <- readArray g_hist (c - c')
            forM_ added $ \i -> VM.write bs i True
            forM_ removed $ \i -> VM.write bs i False
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


-- | Minimize Σ_{i=1}^n wi xi subject to Σ_{i=1}^n wi x≥ l and xi ∈ {0,1}.
--
-- Note: 0 (resp. 1) is identified with False (resp. True) in the assignment.
minSubsetSum
  :: V.Vector v Weight
  => v Weight -- ^ weights @[w1, w2 .. wn]@
  -> Weight -- ^ @l@
  -> Maybe (Weight, VU.Vector Bool)
  -- ^
  -- * the objective value Σ_{i=1}^n wi xi, and
  --
  -- * the assignment @[x1, x2 .. xn]@, identifying 0 (resp. 1) with @False@ (resp. @True@).
minSubsetSum w l
  | wsum < fromIntegral l = Nothing
  | fromIntegral (maxBound :: Int) < wsum =
      error $ "SubsetSum.minSubsetSum: sum of weights " ++ show wsum ++ " is too big to be fitted in Int"
  | otherwise =
      case maxSubsetSum w (fromIntegral wsum - l) of
        (obj, bs) -> Just (fromIntegral wsum - obj, V.map not bs)
  where
    -- Integer is used to avoid integer overflow
    wsum :: Integer
    wsum = V.foldl' (\r x -> r + fromIntegral x) 0 w
  
{-
minimize Σ wi xi = Σ wi (1 - ¬xi) = Σ wi - (Σ wi ¬xi)
subject to Σ wi xi ≥ n

maximize Σ wi ¬xi
subject to Σ wi ¬xi ≤ (Σ wi) - n

Σ wi xi ≥ n
Σ wi (1 - ¬xi) ≥ n
(Σ wi) - (Σ wi ¬xi) ≥ n
(Σ wi ¬xi) ≤ (Σ wi) - n
-}

-- | Solve Σ_{i=1}^n wi x = c and xi ∈ {0,1}.
--
-- Note that this is different from usual definition of the subset sum problem,
-- as this definition allows all xi to be zero.
-- 
-- Note: 0 (resp. 1) is identified with False (resp. True) in the assignment.
subsetSum
  :: V.Vector v Weight
  => v Weight -- ^ weights @[w1, w2 .. wn]@
  -> Weight -- ^ @l@
  -> Maybe (VU.Vector Bool)
  -- ^
  -- the assignment @[x1, x2 .. xn]@, identifying 0 (resp. 1) with @False@ (resp. @True@).
subsetSum w c
  | c' < 0 = Nothing
  | otherwise = assert (c' < fromIntegral (maxBound :: Weight)) $
      fmap (VU.imap (\i x -> if (w V.! i) < 0 then not x else x)) $ subsetSum' w' (fromIntegral c')
{-
      case maxSubsetSum w' (fromIntegral c') of 
        (obj,xs')
          | obj /= fromIntegral c' -> Nothing
          | otherwise -> Just $! VU.imap (\i x -> if (w V.! i) < 0 then not x else x) xs'
-}
  where
    w' = VU.generate (V.length w) (\i -> abs (w V.! i))
    offset :: Integer
    offset = V.foldl' (\a b -> if b < 0 then a + fromIntegral b else a) 0 w
    c' :: Integer
    c' = fromIntegral c - offset

subsetSum'
  :: VU.Vector Weight
  -> Weight
  -> Maybe (VU.Vector Bool)
subsetSum' w c = go 0 (IntMap.singleton 0 [])
  where
    go :: Int -> IntMap [Int] -> Maybe (VU.Vector Bool)
    go !i !m =
      case IntMap.lookup c m of
        Just sol -> Just $! VU.create $ do
          xs <- VM.replicate (V.length w) False
          forM_ sol $ \i -> VM.write xs i True
          return xs
        Nothing
          | i >= V.length w -> Nothing
          | otherwise ->
              let wi = w V.! i
                  m' = m `IntMap.union` IntMap.fromDistinctAscList [(x', i:sol) | (x,sol) <- IntMap.toAscList m, let x' = x + wi, 0 <= x', x' <= c]
              in go (i+1) m'
