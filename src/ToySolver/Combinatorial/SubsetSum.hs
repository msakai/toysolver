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
  -> Maybe (Weight, VU.Vector Bool)
  -- ^
  -- * the objective value Σ_{i=1}^n wi xi, and
  --
  -- * the assignment @[x1, x2 .. xn]@, identifying 0 (resp. 1) with @False@ (resp. @True@).
maxSubsetSum w c =
  case normalizeWeightsToPositive (w,c) of
    (w2, c2, trans)
      | c2 < 0 -> Nothing
      | otherwise -> Just $ trans $ step2 w2 c2
  where
    step2 :: VU.Vector Weight -> Weight -> (Weight, VU.Vector Bool)
    step2 w c
      | V.all (<=c) w = maxSubsetSum' w c
      | otherwise =
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

normalizeWeightsToPositive
  :: V.Vector v Weight
  => (v Weight, Weight)
  -> (VU.Vector Weight, Weight, (Weight, VU.Vector Bool) -> (Weight, VU.Vector Bool))
normalizeWeightsToPositive (w,c)
  | V.all (>=0) w = (V.convert w, c, id)
  | otherwise = runST $ do
      w2 <- VM.new (V.length w)
      let loop !i !offset
            | i >= V.length w = return offset
            | otherwise = do
                let wi = w ! i
                if wi == minBound then
                  error ("ToySolver.Combinatorial.SubsetSum: cannot negate " ++ show wi)
                else if wi < 0 then do
                  VM.write w2 i (- wi)
                  loop (i+1) (offset + fromIntegral wi)
                else do
                  VM.write w2 i wi
                  loop (i+1) offset
      w2 <- V.unsafeFreeze w2
      offset <- loop 0 (0::Integer)
                
      when (fromIntegral (maxBound :: Weight) < fromIntegral c - offset) $
        error ("ToySolver.Combinatorial.SubsetSum: overflow")
      let trans (obj, bs) = (obj + fromIntegral offset, bs2)
            where
              bs2 = VU.imap (\i bi -> if w ! i < 0 then not bi else bi) bs
      return (w2, c - fromIntegral offset, trans)

maxSubsetSum' :: V.Vector v Weight => v Weight -> Weight -> (Weight, VU.Vector Bool)
maxSubsetSum' w !c
  | wsum <= fromIntegral c = (fromIntegral wsum, V.replicate n True)
  | otherwise = assert (wbar <= c) $ assert (wbar + (w ! b) > c) $ body b (b-1) gs_init ft_init True
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

    -- f_{b-1}
    ft_init :: IntMap [Int]
    ft_init = IntMap.singleton 0 []

    -- g_{b}
    gs_init :: IntMap [Int]
    gs_init = IntMap.singleton wbar []

    -- Given t and f_{t-1}, compute f_t.
    ft_update :: Int -> IntMap [Int] -> IntMap [Int]
    ft_update t ft = ft `IntMap.union` m
      where
        wt = w ! t
        m = splitLE (snd f_range) $ IntMap.mapKeysMonotonic (+wt) $ IntMap.map (t :) ft

    -- Given s and g_{s+1}, compute g_s.
    gs_update :: Int -> IntMap [Int] -> IntMap [Int]
    gs_update s gs = gs `IntMap.union` m2
      where
        ws = w ! s
        m1 = IntMap.mapKeysMonotonic (subtract ws) $  IntMap.map (s :) gs
        m2 =
          case IntMap.splitLookup (fst g_range) m1 of
            (_, Just v, hi) -> IntMap.insert (fst g_range) v m1
            (lo, Nothing, hi)
              | IntMap.null lo -> hi
              | otherwise ->
                  case IntMap.findMax lo of
                    (k,v) -> IntMap.insert k v hi

    compute_best :: IntMap [Int] -> IntMap [Int] -> (Int, [Int], [Int])
    compute_best gs ft = runST $ do
      objRef <- newSTRef (-1, undefined, undefined)
      let loop [] _ = return ()
          loop _ [] = return ()
          loop xxs@((gobj,gsol):xs) yys@((fobj,fsol):ys)
            | c < gobj + fobj = loop xs yys
            | otherwise = do
                (curr, _, _) <- readSTRef objRef
                when (curr < gobj + fobj) $ writeSTRef objRef (gobj + fobj, gsol, fsol)
                loop xxs ys
      loop (IntMap.toDescList gs) (IntMap.toAscList ft)
      readSTRef objRef

    build :: [Int] -> [Int] -> VU.Vector Bool
    build gsol fsol = V.create $ do
      bs <- VM.new n
      forM_ [0..b-1] $ \i -> VM.write bs i True
      forM_ [b..n-1] $ \i -> VM.write bs i False
      forM_ fsol $ \i -> VM.write bs i True
      forM_ gsol $ \i -> VM.write bs i False
      return bs

    body :: Int -> Int -> IntMap [Int] -> IntMap [Int] -> Bool -> (Weight, VU.Vector Bool)
    body !s !t !gs !ft !flag
      | obj == c || (s == 0 && t == n-1) = (obj, build gsol fsol)
      | s == 0   = b1
      | t == n-1 = b2
      | otherwise = if flag then b2 else b1
      where
        (obj, gsol, fsol) = compute_best gs ft
        b1 = body s (t+1) gs (ft_update (t+1) ft) (not flag)
        b2 = body (s-1) t (gs_update (s-1) gs) ft (not flag)      

splitLE :: Int -> IntMap v -> IntMap v
splitLE k m =
  case IntMap.splitLookup k m of
    (lo, Nothing, _) -> lo
    (lo, Just v, _) -> IntMap.insert k v lo

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
  | wsum < fromIntegral (minBound :: Int) || fromIntegral (maxBound :: Int) < wsum =
      error $ "SubsetSum.minSubsetSum: sum of weights " ++ show wsum ++ " do not fit into Int"
  | otherwise =
      case maxSubsetSum w (fromIntegral wsum - l) of
        Nothing -> Nothing
        Just (obj, bs) -> Just (fromIntegral wsum - obj, V.map not bs)
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
  | fromIntegral (maxBound :: Weight) < c' = error ("ToySolver.Combinatorial.SubsetSum: overflow")
  | otherwise = fmap (VU.imap (\i x -> if (w V.! i) < 0 then not x else x)) $ subsetSum' w' (fromIntegral c')
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
