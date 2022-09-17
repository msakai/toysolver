{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Encoder.PB.Internal.Adder
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
module ToySolver.SAT.Encoder.PB.Internal.Adder
  ( addPBLinAtLeastAdder
  , encodePBLinAtLeastAdder
  ) where

import Control.Monad
import Control.Monad.Primitive
import Data.Bits
import Data.Maybe
import Data.Primitive.MutVar
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import ToySolver.Data.Boolean
import qualified ToySolver.Internal.Data.SeqQueue as SQ
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import ToySolver.SAT.Encoder.Tseitin (Formula (..))

addPBLinAtLeastAdder :: forall m. PrimMonad m => Tseitin.Encoder m -> SAT.PBLinAtLeast -> m ()
addPBLinAtLeastAdder enc constr = do
  formula <- encodePBLinAtLeastAdder' enc constr
  Tseitin.addFormula enc formula

encodePBLinAtLeastAdder :: PrimMonad m => Tseitin.Encoder m -> SAT.PBLinAtLeast -> m SAT.Lit
encodePBLinAtLeastAdder enc constr = do
  formula <- encodePBLinAtLeastAdder' enc constr
  Tseitin.encodeFormula enc formula

encodePBLinAtLeastAdder' :: PrimMonad m => Tseitin.Encoder m -> SAT.PBLinAtLeast -> m Tseitin.Formula
encodePBLinAtLeastAdder' _ (_,rhs) | rhs <= 0 = return true
encodePBLinAtLeastAdder' enc (lhs,rhs) = do
  lhs1 <- encodePBLinSumAdder enc lhs
  let rhs1 = bits rhs
  if length lhs1 < length rhs1 then do
    return false
  else do
    let lhs2 = reverse lhs1
        rhs2 = replicate (length lhs1 - length rhs1) False ++ reverse rhs1
        f [] = true
        f ((x,False) : xs) = Atom x .||. f xs
        f ((x,True) : xs) = Atom x .&&. f xs
    return $ f (zip lhs2 rhs2)
  where
    bits :: Integer -> [Bool]
    bits n = f n 0
      where
        f 0 !_ = []
        f n i = testBit n i : f (clearBit n i) (i+1)

encodePBLinSumAdder :: forall m. PrimMonad m => Tseitin.Encoder m -> SAT.PBLinSum -> m [SAT.Lit]
encodePBLinSumAdder enc lhs = do
  (buckets :: MutVar (PrimState m) (Seq (SQ.SeqQueue m SAT.Lit))) <- newMutVar Seq.empty
  let insert :: Int -> Int -> m ()
      insert i x = do
        bs <- readMutVar buckets
        let n = Seq.length bs
        q <- if i < n then do
               return $ Seq.index bs i
             else do
               qs <- replicateM (i+1 - n) SQ.newFifo
               let bs' = bs Seq.>< Seq.fromList qs
               writeMutVar buckets bs'
               return $ Seq.index bs' i
        SQ.enqueue q x

      bits :: Integer -> [Int]
      bits n = f n 0
        where
          f 0 !_ = []
          f n i
            | testBit n i = i : f (clearBit n i) (i+1)
            | otherwise = f n (i+1)

  forM_ lhs $ \(c,x) -> do
    forM_ (bits c) $ \i -> insert i x

  let loop i ret = do
        bs <- readMutVar buckets
        let n = Seq.length bs
        if i >= n then do
          return $ reverse ret
        else do
          let q = Seq.index bs i
          m <- SQ.queueSize q
          case m of
            0 -> do
              b <- Tseitin.encodeDisj enc [] -- False
              loop (i+1) (b : ret)
            1 -> do
              b <- fromJust <$> SQ.dequeue q
              loop (i+1) (b : ret)
            2 -> do
              b1 <- fromJust <$> SQ.dequeue q
              b2 <- fromJust <$> SQ.dequeue q
              s <- encodeHASum enc b1 b2
              c <- encodeHACarry enc b1 b2
              insert (i+1) c
              loop (i+1) (s : ret)
            _ -> do
              b1 <- fromJust <$> SQ.dequeue q
              b2 <- fromJust <$> SQ.dequeue q
              b3 <- fromJust <$> SQ.dequeue q
              s <- Tseitin.encodeFASum enc b1 b2 b3
              c <- Tseitin.encodeFACarry enc b1 b2 b3
              insert i s
              insert (i+1) c
              loop i ret
  loop 0 []

encodeHASum :: PrimMonad m => Tseitin.Encoder m -> SAT.Lit -> SAT.Lit -> m SAT.Lit
encodeHASum = Tseitin.encodeXOR

encodeHACarry :: PrimMonad m => Tseitin.Encoder m -> SAT.Lit -> SAT.Lit -> m SAT.Lit
encodeHACarry enc a b = Tseitin.encodeConj enc [a,b]
