{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Encoder.Cardinality.Internal.ParallelCounter
-- Copyright   :  (c) Masahiro Sakai 2019
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Encoder.Cardinality.Internal.ParallelCounter
  ( addAtLeastParallelCounter
  , encodeAtLeastWithPolarityParallelCounter
  ) where

import Control.Monad.Primitive
import Control.Monad.State.Strict
import Data.Bits
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin

addAtLeastParallelCounter :: PrimMonad m => Tseitin.Encoder m -> SAT.AtLeast -> m ()
addAtLeastParallelCounter enc constr = do
  l <- encodeAtLeastWithPolarityParallelCounter enc Tseitin.polarityPos constr
  SAT.addClause enc [l]

encodeAtLeastWithPolarityParallelCounter :: forall m. PrimMonad m => Tseitin.Encoder m -> Tseitin.Polarity -> SAT.AtLeast -> m SAT.Lit
encodeAtLeastWithPolarityParallelCounter enc polarity (lhs,rhs) = do
  if rhs <= 0 then
    Tseitin.encodeConjWithPolarity enc polarity []
  else if length lhs < rhs then
    Tseitin.encodeDisjWithPolarity enc polarity []
  else do
    let rhs_bits = bits (fromIntegral rhs)
    (cnt, overflowBits) <- encodeSumParallelCounter enc (length rhs_bits) lhs
    isGE <- encodeGE enc polarity cnt rhs_bits
    Tseitin.encodeDisjWithPolarity enc polarity $ isGE : overflowBits
  where
    bits :: Integer -> [Bool]
    bits n = f n 0
      where
        f 0 !_ = []
        f n i = testBit n i : f (clearBit n i) (i+1)

encodeSumParallelCounter :: forall m. PrimMonad m => Tseitin.Encoder m -> Int -> [SAT.Lit] -> m ([SAT.Lit], [SAT.Lit])
encodeSumParallelCounter enc w lits = do
  let add :: [SAT.Lit] -> [SAT.Lit] -> SAT.Lit -> StateT [SAT.Lit] m [SAT.Lit]
      add = go 0 []
        where
          go :: Int -> [SAT.Lit] -> [SAT.Lit] -> [SAT.Lit] -> SAT.Lit -> StateT [SAT.Lit] m [SAT.Lit]
          go i ret _xs _ys c | i == w = do
            modify (c:)
            return $ reverse ret
          go _i ret [] [] c = return $ reverse (c : ret)
          go i ret (x : xs) (y : ys) c = do
            z <- lift $ Tseitin.encodeFASum enc x y c
            c' <- lift $ Tseitin.encodeFACarry enc x y c
            go (i+1) (z : ret) xs ys c'
          go _ _ _ _ _ = error "encodeSumParallelCounter: should not happen"

      f :: Vector SAT.Lit -> StateT [SAT.Lit] m [SAT.Lit]
      f xs
        | V.null xs = return []
        | otherwise = do
            let len2 = V.length xs `div` 2
            cnt1 <- f (V.slice 0 len2 xs)
            cnt2 <- f (V.slice len2 len2 xs)
            c <- if V.length xs `mod` 2 == 0 then
                   lift $ Tseitin.encodeDisj enc []
                 else
                   lift $ return $ xs V.! (V.length xs - 1)
            add cnt1 cnt2 c

  runStateT (f (V.fromList lits)) []

encodeGE :: forall m. PrimMonad m => Tseitin.Encoder m -> Tseitin.Polarity -> [SAT.Lit] -> [Bool] -> m SAT.Lit
encodeGE enc polarity lhs rhs = do
  let f :: [SAT.Lit] -> [Bool] -> SAT.Lit -> m SAT.Lit
      f [] [] r = return r
      f [] (True  : _) _ = Tseitin.encodeDisjWithPolarity enc polarity [] -- false
      f [] (False : bs) r = f [] bs r
      f (l : ls) (True  : bs) r = do
        f ls bs =<< Tseitin.encodeConjWithPolarity enc polarity [l, r]
      f (l : ls) (False : bs) r = do
        f ls bs =<< Tseitin.encodeDisjWithPolarity enc polarity [l, r]
      f (l : ls) [] r = do
        f ls [] =<< Tseitin.encodeDisjWithPolarity enc polarity [l, r]
  t <- Tseitin.encodeConjWithPolarity enc polarity [] -- true
  f lhs rhs t
