{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Encoder.PB.Internal.Sorter
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- References:
--
-- * [ES06] N. Eén and N. Sörensson. Translating Pseudo-Boolean
--   Constraints into SAT. JSAT 2:1–26, 2006.
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Encoder.PB.Internal.Sorter
  ( Base
  , UDigit
  , UNumber
  , encode
  , decode

  , Cost
  , optimizeBase

  , genSorterCircuit
  , sortVector

  , addPBLinAtLeastSorter
  , encodePBLinAtLeastSorter
  ) where

import Control.Monad.Primitive
import Control.Monad.State
import Control.Monad.Writer
import Data.Maybe
import Data.Vector (Vector, (!))
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import ToySolver.Data.BoolExpr
import ToySolver.Data.Boolean
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin

-- ------------------------------------------------------------------------
-- Circuit-like implementation of Batcher's odd-even mergesort

genSorterCircuit :: Int -> [(Int,Int)]
genSorterCircuit len = execWriter (mergeSort (V.iterateN len (+1) 0)) []
  where
    genCompareAndSwap i j = tell ((i,j) :)

    mergeSort is
      | V.length is <= 1 = return ()
      | V.length is == 2 = genCompareAndSwap (is!0) (is!1)
      | otherwise =
          case halve is of
            (is1,is2) -> do
              mergeSort is1
              mergeSort is2
              oddEvenMerge is

    oddEvenMerge is
      | V.length is <= 1 = return ()
      | V.length is == 2 = genCompareAndSwap (is!0) (is!1)
      | otherwise =
          case splitOddEven is of
            (os,es) -> do
              oddEvenMerge os
              oddEvenMerge es
              forM_ [2,3 .. V.length is-1] $ \i -> do
                genCompareAndSwap (is!(i-1)) (is!i)

halve :: Vector a -> (Vector a, Vector a)
halve v
  | V.length v <= 1 = (v, V.empty)
  | otherwise = (V.slice 0 len1 v, V.slice len1 len2 v)
      where
        n = head $ dropWhile (< V.length v) $ iterate (*2) 1
        len1 = n `div` 2
        len2 = V.length v - len1

splitOddEven :: Vector a -> (Vector a, Vector a)
splitOddEven v = (V.generate len1 (\i -> v V.! (i*2+1)), V.generate len2 (\i -> v V.! (i*2)))
  where
    len1 = V.length v `div` 2
    len2 = (V.length v + 1) `div` 2

sortVector :: (Ord a) => Vector a -> Vector a
sortVector v = V.create $ do
  m <- V.thaw v
  forM_ (genSorterCircuit (V.length v)) $ \(i,j) -> do
    vi <- MV.read m i
    vj <- MV.read m j
    when (vi > vj) $ do
      MV.write m i vj
      MV.write m j vi
  return m

-- ------------------------------------------------------------------------

type Base = [Int]
type UDigit = Int
type UNumber = [UDigit]

encode :: Base -> Integer -> UNumber
encode _ 0 = []
encode [] x
  | x <= fromIntegral (maxBound :: UDigit) = [fromIntegral x]
  | otherwise = undefined
encode (b:bs) x = fromIntegral (x `mod` fromIntegral b) : encode bs (x `div` fromIntegral b)

decode :: Base -> UNumber -> Integer
decode _ [] = 0
decode [] [x] = fromIntegral x
decode (b:bs) (x:xs) = fromIntegral x + fromIntegral b * decode bs xs

{-
test1 = encode [3,5] 164 -- [2,4,10]
test2 = decode [3,5] [2,4,10] -- 164

test3 = optimizeBase [1,1,2,2,3,3,3,3,7]
-}

-- ------------------------------------------------------------------------

type Cost = Integer

primes :: [Int]
primes = [2, 3, 5, 7, 11, 13, 17]

optimizeBase :: [Integer] -> Base
optimizeBase xs = reverse $ fst $ fromJust $ execState (m xs [] 0) Nothing
  where
    m :: [Integer] -> Base -> Integer -> State (Maybe (Base, Cost)) ()
    m xs base cost = do
      best <- get
      case best of
        Just (_bestBase, bestCost) | bestCost < cost -> return ()
        _ -> do
          let cost' = cost + sum xs
          case best of
            Just (_bestBase, bestCost) | cost' < bestCost ->
              put $ Just (base, cost')
            Nothing ->
              put $ Just (base, cost')
            _ -> return ()
          unless (null xs) $ do
            forM_ primes $ \p -> do
              m [d | x <- xs, let d = x `div` fromIntegral p, d > 0]
                (p : base)
                (cost + sum [r | x <- xs, let r = x `mod` fromIntegral p])

-- ------------------------------------------------------------------------

addPBLinAtLeastSorter :: PrimMonad m => Tseitin.Encoder m -> SAT.PBLinAtLeast -> m ()
addPBLinAtLeastSorter enc constr = do
  formula <- encodePBLinAtLeastSorter' enc constr
  Tseitin.addFormula enc formula

encodePBLinAtLeastSorter :: PrimMonad m => Tseitin.Encoder m -> SAT.PBLinAtLeast -> m SAT.Lit
encodePBLinAtLeastSorter enc constr = do
  formula <- encodePBLinAtLeastSorter' enc constr
  Tseitin.encodeFormula enc formula

encodePBLinAtLeastSorter' :: PrimMonad m => Tseitin.Encoder m -> SAT.PBLinAtLeast -> m Tseitin.Formula
encodePBLinAtLeastSorter' enc (lhs,rhs) = do
  let base = optimizeBase [c | (c,_) <- lhs]
  sorters <- genSorters enc base [(encode base c, l) | (c,l) <- lhs] []
  return $ lexComp base sorters (encode base rhs)

genSorters :: PrimMonad m => Tseitin.Encoder m -> Base -> [(UNumber, SAT.Lit)] -> [SAT.Lit] -> m [Vector SAT.Lit]
genSorters enc base lhs carry = do
  let is = V.fromList carry <> V.concat [V.replicate (fromIntegral d) l | (d:_,l) <- lhs, d /= 0]
  buf <- V.thaw is
  forM_ (genSorterCircuit (V.length is)) $ \(i,j) -> do
    vi <- MV.read buf i
    vj <- MV.read buf j
    MV.write buf i =<< Tseitin.encodeDisj enc [vi,vj]
    MV.write buf j =<< Tseitin.encodeConj enc [vi,vj]
  os <- V.freeze buf
  case base of
    [] -> return [os]
    b:bs -> do
      oss <- genSorters enc bs [(ds,l) | (_:ds,l) <- lhs] [os!(i-1) | i <- takeWhile (<= V.length os) (iterate (+b) b)]
      return $ os : oss

isGE :: Vector SAT.Lit -> Int -> Tseitin.Formula
isGE out lim
  | lim <= 0 = true
  | lim - 1 < V.length out = Atom $ out ! (lim - 1)
  | otherwise = false

isGEMod :: Int -> Vector SAT.Lit -> Int -> Tseitin.Formula
isGEMod _n _out lim | lim <= 0 = true
isGEMod n out lim =
  orB [isGE out (j + lim) .&&. notB isGE out (j + n) | j <- [0, n .. V.length out - 1]]

lexComp :: Base -> [Vector SAT.Lit] -> UNumber -> Tseitin.Formula
lexComp base lhs rhs = f true base lhs rhs
  where
    f ret (b:bs) (out:os) ds = f (gt .||. (ge .&&. ret)) bs os (drop 1 ds)
      where
        d = if null ds then 0 else head ds
        gt = isGEMod b out (d+1)
        ge = isGEMod b out d
    f ret [] [out] ds = gt .||. (ge .&&. ret)
      where
        d = if null ds then 0 else head ds
        gt = isGE out (d+1)
        ge = isGE out d

-- ------------------------------------------------------------------------
