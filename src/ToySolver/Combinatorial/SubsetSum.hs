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
import Control.Monad
import Control.Monad.ST
import Data.STRef
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Vector.Generic ((!))
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Generic.Mutable as VM
import qualified Data.Vector.Unboxed as VU

type Weight = Integer

-- | Maximize Σ_{i=1}^n wi xi subject to Σ_{i=1}^n wi xi ≤ c and xi ∈ {0,1}.
--
-- Note: 0 (resp. 1) is identified with False (resp. True) in the assignment.
maxSubsetSum
  :: VG.Vector v Weight
  => v Weight -- ^ weights @[w1, w2 .. wn]@
  -> Weight -- ^ capacity @c@
  -> Maybe (Weight, VU.Vector Bool)
  -- ^
  -- * the objective value Σ_{i=1}^n wi xi, and
  --
  -- * the assignment @[x1, x2 .. xn]@, identifying 0 (resp. 1) with @False@ (resp. @True@).
maxSubsetSum w c =
  case normalizeWeightsToPositive (w,c) of
    (w1, c1, trans1)
      | c1 < 0 -> Nothing
      | otherwise ->
          case normalize2 (w1, c1) of
            (w2, c2, trans2) ->
              case normalizeGCDLe (w2, c2) of
                (w3, c3, trans3) ->
                  Just $ trans1 $ trans2 $ trans3 $ maxSubsetSum' w3 c3

normalizeWeightsToPositive
  :: VG.Vector v Weight
  => (v Weight, Weight)
  -> (V.Vector Weight, Weight, (Weight, VU.Vector Bool) -> (Weight, VU.Vector Bool))
normalizeWeightsToPositive (w,c)
  | VG.all (>=0) w = (VG.convert w, c, id)
  | otherwise = runST $ do
      w2 <- VM.new (VG.length w)
      let loop !i !offset
            | i >= VG.length w = return offset
            | otherwise = do
                let wi = w ! i
                if wi < 0 then do
                  VM.write w2 i (- wi)
                  loop (i+1) (offset + wi)
                else do
                  VM.write w2 i wi
                  loop (i+1) offset
      offset <- loop 0 (0::Integer)
      w2 <- VG.unsafeFreeze w2
      let trans (obj, bs) = (obj + offset, bs2)
            where
              bs2 = VU.imap (\i bi -> if w ! i < 0 then not bi else bi) bs
      return (w2, c - offset, trans)

normalize2
  :: (V.Vector Weight, Weight)
  -> (V.Vector Weight, Weight, (Weight, VU.Vector Bool) -> (Weight, VU.Vector Bool))
normalize2 (w,c)
  | VG.all (\wi -> 0<wi && wi<=c) w = (w, c, id)
  | otherwise = (VG.filter (\wi -> 0<wi && wi<=c) w, c, trans)
  where
    trans (obj, bs) = (obj, bs2)
      where
        bs2 = VU.create $ do
          v <- VM.new (VG.length w)
          let loop !i !j =
                when (i < VG.length w) $ do
                  let wi = w ! i
                  if 0 < wi && wi <= c then do
                    VM.write v i (bs ! j)
                    loop (i+1) (j+1)
                  else do
                    VM.write v i False
                    loop (i+1) j
          loop 0 0
          return v

normalizeGCDLe
  :: (V.Vector Weight, Weight)
  -> (V.Vector Weight, Weight, (Weight, VU.Vector Bool) -> (Weight, VU.Vector Bool))
normalizeGCDLe (w,c)
  | VG.null w || d == 1 = (w, c, id)
  | otherwise = (VG.map (`div` d) w, c `div` d, trans)
  where
    d = VG.foldl1' gcd w
    trans (obj, bs) = (obj * d, bs)

normalizeGCDEq
  :: (V.Vector Weight, Weight)
  -> Maybe (V.Vector Weight, Weight, (Weight, VU.Vector Bool) -> (Weight, VU.Vector Bool))
normalizeGCDEq (w,c)
  | VG.null w || d == 1 = Just (w, c, id)
  | c `mod` d == 0 = Just (VG.map (`div` d) w, c `div` d, trans)
  | otherwise = Nothing
  where
    d = VG.foldl1' gcd w
    trans (obj, bs) = (obj * d, bs)

maxSubsetSum' :: V.Vector Weight -> Weight -> (Weight, VU.Vector Bool)
maxSubsetSum' !w !c
  | wsum <= c = (wsum, VG.replicate (VG.length w) True)
  | c <= fromIntegral (maxBound :: Int) =
      maxSubsetSumInt' (VG.generate (VG.length w) (\i -> fromIntegral (w VG.! i))) (fromIntegral c) wsum
  | otherwise =
      maxSubsetSumInteger' w c wsum
  where
    wsum = VG.sum w
                      
maxSubsetSumInteger' :: V.Vector Weight -> Weight -> Weight -> (Weight, VU.Vector Bool)
maxSubsetSumInteger' w !c wsum = assert (wbar <= c) $ assert (wbar + (w ! b) > c) $ runST $ do
  objRef <- newSTRef (wbar, [], [])
  let updateObj gs ft = do
        let loop [] _ = return ()
            loop _ [] = return ()
            loop xxs@((gobj,gsol):xs) yys@((fobj,fsol):ys)
              | c < gobj + fobj = loop xs yys
              | otherwise = do
                  (curr, _, _) <- readSTRef objRef
                  when (curr < gobj + fobj) $ writeSTRef objRef (gobj + fobj, gsol, fsol)
                  loop xxs ys
        loop (Map.toDescList gs) (Map.toAscList ft)

  let loop !s !t !gs !ft !flag = do
        (obj, gsol, fsol) <- readSTRef objRef
        if obj == c || (s == 0 && t == n-1) then do
          let sol = VG.create $ do
                bs <- VM.new n
                forM_ [0..b-1] $ \i -> VM.write bs i True
                forM_ [b..n-1] $ \i -> VM.write bs i False
                forM_ fsol $ \i -> VM.write bs i True
                forM_ gsol $ \i -> VM.write bs i False
                return bs
          return (obj, sol)
        else do
          let updateF = do
                -- Compute f_{t+1} from f_t
                let t' = t + 1
                    wt' = w ! t'
                    m = Map.mapKeysMonotonic (+ wt') $ Map.map (t' :) $ splitLE (c - wt') ft
                    ft' = ft `Map.union` m
                updateObj gs m
                loop s t' gs ft' (not flag)
              updateG = do
                -- Compute g_{s-1} from g_s
                let s' = s - 1
                    ws = w ! s'
                    m = Map.map (s' :) $ g_drop $ Map.mapKeysMonotonic (subtract ws) $ gs
                    gs' = gs `Map.union` m
                updateObj m ft
                loop s' t gs' ft (not flag)
          if s == 0 then
            updateF
          else if t == n-1 then
            updateG
          else
            if flag then updateG else updateF

  let -- f_{b-1}
      fb' :: Map Integer [Int]
      fb' = Map.singleton 0 []
      -- g_{b}
      gb :: Map Integer [Int]
      gb = Map.singleton wbar []
  loop b (b-1) gb fb' True

  where
    n = VG.length w

    b :: Int
    b = loop (-1) 0
      where
        loop :: Int -> Integer -> Int
        loop !i !s
          | s > c = i
          | otherwise = loop (i+1) (s + (w ! (i+1)))

    wbar :: Weight
    wbar = VG.sum $ VG.slice 0 b w

    max_f :: Weight
    max_f = wsum - fromIntegral wbar

    min_g :: Weight
    min_g = 0 `max` (c - max_f)

    g_drop :: Map Integer [Int] -> Map Integer [Int]
    g_drop g =
      case Map.splitLookup min_g g of
        (lo, _, _) | Map.null lo -> g
        (_, Just v, hi) -> Map.insert min_g v hi
        (lo, Nothing, hi) ->
          case Map.findMax lo of
            (k,v) -> Map.insert k v hi

    splitLE :: Ord k => k -> Map k v -> Map k v
    splitLE k m =
      case Map.splitLookup k m of
        (lo, Nothing, _) -> lo
        (lo, Just v, _) -> Map.insert k v lo

maxSubsetSumInt' :: VU.Vector Int -> Int -> Weight -> (Weight, VU.Vector Bool)
maxSubsetSumInt' w !c wsum = assert (wbar <= c) $ assert (wbar + (w ! b) > c) $ runST $ do
  objRef <- newSTRef (wbar, [], [])
  let updateObj gs ft = do
        let loop [] _ = return ()
            loop _ [] = return ()
            loop xxs@((gobj,gsol):xs) yys@((fobj,fsol):ys)
              | c < gobj + fobj = loop xs yys
              | otherwise = do
                  (curr, _, _) <- readSTRef objRef
                  when (curr < gobj + fobj) $ writeSTRef objRef (gobj + fobj, gsol, fsol)
                  loop xxs ys
        loop (IntMap.toDescList gs) (IntMap.toAscList ft)

  let loop !s !t !gs !ft !flag = do
        (obj, gsol, fsol) <- readSTRef objRef
        if obj == c || (s == 0 && t == n-1) then do
          let sol = VG.create $ do
                bs <- VM.new n
                forM_ [0..b-1] $ \i -> VM.write bs i True
                forM_ [b..n-1] $ \i -> VM.write bs i False
                forM_ fsol $ \i -> VM.write bs i True
                forM_ gsol $ \i -> VM.write bs i False
                return bs
          return (fromIntegral obj, sol)
        else do
          let updateF = do
                -- Compute f_{t+1} from f_t
                let t' = t + 1
                    wt' = w ! t'
                    m = IntMap.mapKeysMonotonic (+ wt') $ IntMap.map (t' :) $ splitLE (c - wt') ft
                    ft' = ft `IntMap.union` m
                updateObj gs m
                loop s t' gs ft' (not flag)
              updateG = do
                -- Compute g_{s-1} from g_s
                let s' = s - 1
                    ws = w ! s'
                    m = IntMap.map (s' :) $ g_drop $ IntMap.mapKeysMonotonic (subtract ws) $ gs
                    gs' = gs `IntMap.union` m
                updateObj m ft
                loop s' t gs' ft (not flag)
          if s == 0 then
            updateF
          else if t == n-1 then
            updateG
          else
            if flag then updateG else updateF

  let -- f_{b-1}
      fb' :: IntMap [Int]
      fb' = IntMap.singleton 0 []
      -- g_{b}
      gb :: IntMap [Int]
      gb = IntMap.singleton wbar []
  loop b (b-1) gb fb' True

  where
    n = VG.length w

    b :: Int
    b = loop (-1) 0
      where
        loop :: Int -> Integer -> Int
        loop !i !s
          | s > fromIntegral c = i
          | otherwise = loop (i+1) (s + fromIntegral (w ! (i+1)))

    wbar :: Int
    wbar = VG.sum $ VG.slice 0 b w

    max_f :: Integer
    max_f = wsum - fromIntegral wbar

    min_g :: Int
    min_g = if max_f < fromIntegral c then c - fromIntegral max_f else 0

    g_drop :: IntMap [Int] -> IntMap [Int]
    g_drop g =
      case IntMap.splitLookup min_g g of
        (lo, _, _) | IntMap.null lo -> g
        (_, Just v, hi) -> IntMap.insert min_g v hi
        (lo, Nothing, hi) ->
          case IntMap.findMax lo of
            (k,v) -> IntMap.insert k v hi

    splitLE :: Int -> IntMap v -> IntMap v
    splitLE k m =
      case IntMap.splitLookup k m of
        (lo, Nothing, _) -> lo
        (lo, Just v, _) -> IntMap.insert k v lo
                           
-- | Minimize Σ_{i=1}^n wi xi subject to Σ_{i=1}^n wi x≥ l and xi ∈ {0,1}.
--
-- Note: 0 (resp. 1) is identified with False (resp. True) in the assignment.
minSubsetSum
  :: VG.Vector v Weight
  => v Weight -- ^ weights @[w1, w2 .. wn]@
  -> Weight -- ^ @l@
  -> Maybe (Weight, VU.Vector Bool)
  -- ^
  -- * the objective value Σ_{i=1}^n wi xi, and
  --
  -- * the assignment @[x1, x2 .. xn]@, identifying 0 (resp. 1) with @False@ (resp. @True@).
minSubsetSum w l =
  case maxSubsetSum w (wsum - l) of
    Nothing -> Nothing
    Just (obj, bs) -> Just (wsum - obj, VG.map not bs)
  where
    wsum = VG.sum w
  
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
  :: VG.Vector v Weight
  => v Weight -- ^ weights @[w1, w2 .. wn]@
  -> Weight -- ^ @l@
  -> Maybe (VU.Vector Bool)
  -- ^
  -- the assignment @[x1, x2 .. xn]@, identifying 0 (resp. 1) with @False@ (resp. @True@).
subsetSum w c =
  case normalizeWeightsToPositive (w,c) of
    (w1, c1, trans1)
      | c1 < 0 -> Nothing
      | otherwise ->
          case normalize2 (w1, c1) of
            (w2, c2, trans2) -> do
              (w3, c3, trans3) <- normalizeGCDEq (w2,c2)
              let (obj, sol) = maxSubsetSum' w3 c3
              guard $ obj == c3
              return $ snd $ trans1 $ trans2 $ trans3 (obj, sol)
