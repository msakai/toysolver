{-# LANGUAGE BangPatterns, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Encoder.PB
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (BangPatterns, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses)
--
-- References:
--
-- * [ES06] N . Eéen and N. Sörensson. Translating Pseudo-Boolean
--   Constraints into SAT. JSAT 2:1–26, 2006.
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Encoder.PB
  ( Encoder
  , Strategy (..)
  , newEncoder
  , newEncoderWithStrategy
  , encodePBLinAtLeast
  ) where

import Control.Monad.Primitive
import Control.Monad.State.Strict
import Data.Bits
import Data.Default.Class
import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Ord
import Data.Primitive.MutVar
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import ToySolver.Data.Boolean
import ToySolver.Data.BoolExpr
import qualified ToySolver.Internal.Data.SeqQueue as SQ
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import ToySolver.SAT.Encoder.PB.Internal.Sorter (addPBLinAtLeastSorter, encodePBLinAtLeastSorter)

data Encoder m = Encoder (Tseitin.Encoder m) Strategy

data Strategy
  = BDD
  | Adder
  | Sorter
  | Hybrid -- not implemented yet
  deriving (Show, Eq, Ord, Enum, Bounded)

instance Default Strategy where
  def = Hybrid

newEncoder :: Monad m => Tseitin.Encoder m -> m (Encoder m)
newEncoder tseitin = newEncoderWithStrategy tseitin Hybrid

newEncoderWithStrategy :: Monad m => Tseitin.Encoder m -> Strategy -> m (Encoder m)
newEncoderWithStrategy tseitin strategy = return (Encoder tseitin strategy)

instance Monad m => SAT.NewVar m (Encoder m) where
  newVar   (Encoder a _) = SAT.newVar a
  newVars  (Encoder a _) = SAT.newVars a
  newVars_ (Encoder a _) = SAT.newVars_ a

instance Monad m => SAT.AddClause m (Encoder m) where
  addClause (Encoder a _) = SAT.addClause a

instance PrimMonad m => SAT.AddCardinality m (Encoder m) where
  addAtLeast enc lhs rhs = SAT.addPBAtLeast enc [(1, l) | l <- lhs] (fromIntegral rhs)

instance PrimMonad m => SAT.AddPBLin m (Encoder m) where
  addPBAtLeast enc lhs rhs = do
    let (lhs',rhs') = SAT.normalizePBLinAtLeast (lhs,rhs)
    if rhs' == 1 && and [c==1 | (c,_) <- lhs'] then
      SAT.addClause enc [l | (_,l) <- lhs']
    else do
      addPBLinAtLeast' enc (lhs',rhs')

encodePBLinAtLeast :: forall m. PrimMonad m => Encoder m -> SAT.PBLinAtLeast -> m SAT.Lit
encodePBLinAtLeast enc constr =
  encodePBLinAtLeast' enc $ SAT.normalizePBLinAtLeast constr

-- -----------------------------------------------------------------------

addPBLinAtLeast' :: PrimMonad m => Encoder m -> SAT.PBLinAtLeast -> m ()
addPBLinAtLeast' enc@(Encoder tseitin strategy) = 
  case strategy of
    Adder -> addPBLinAtLeastAdder enc
    Sorter -> addPBLinAtLeastSorter tseitin
    _ -> addPBLinAtLeastBDD enc

encodePBLinAtLeast' :: PrimMonad m => Encoder m -> SAT.PBLinAtLeast -> m SAT.Lit
encodePBLinAtLeast' enc@(Encoder tseitin strategy) = 
  case strategy of
    Adder -> encodePBLinAtLeastAdder enc
    Sorter -> encodePBLinAtLeastSorter tseitin
    _ -> encodePBLinAtLeastBDD enc
  
-- -----------------------------------------------------------------------

addPBLinAtLeastBDD :: PrimMonad m => Encoder m -> SAT.PBLinAtLeast -> m ()
addPBLinAtLeastBDD enc constr = do
  l <- encodePBLinAtLeastBDD enc constr
  SAT.addClause enc [l]

encodePBLinAtLeastBDD :: forall m. PrimMonad m => Encoder m -> SAT.PBLinAtLeast -> m SAT.Lit
encodePBLinAtLeastBDD (Encoder tseitin _) (lhs,rhs) = do
  let lhs' = sortBy (flip (comparing fst)) lhs
  flip evalStateT Map.empty $ do
    let f :: SAT.PBLinSum -> Integer -> Integer -> StateT (Map (SAT.PBLinSum, Integer) SAT.Lit) m SAT.Lit
        f xs rhs slack
          | rhs <= 0  = lift $ Tseitin.encodeConj tseitin [] -- true
          | slack < 0 = lift $ Tseitin.encodeDisj tseitin [] -- false
          | otherwise = do
              m <- get
              case Map.lookup (xs,rhs) m of
                Just l -> return l
                Nothing -> do
                  case xs of
                    [(_,l)] -> return l
                    (c,l) : xs' -> do
                      thenLit <- f xs' (rhs - c) slack
                      l2 <- lift $ Tseitin.encodeConjWithPolarity tseitin Tseitin.polarityPos [l, thenLit]
                      l3 <- if c > slack then
                              return l2
                            else do
                              elseLit <- f xs' rhs (slack - c)
                              lift $ Tseitin.encodeDisjWithPolarity tseitin Tseitin.polarityPos [l2, elseLit]
                      modify (Map.insert (xs,rhs) l3)
                      return l3
    f lhs' rhs (sum [c | (c,_) <- lhs'] - rhs)

-- -----------------------------------------------------------------------

addPBLinAtLeastAdder :: forall m. PrimMonad m => Encoder m -> SAT.PBLinAtLeast -> m ()
addPBLinAtLeastAdder enc@(Encoder tseitin _) constr = do
  formula <- encodePBLinAtLeastAdder' enc constr
  Tseitin.addFormula tseitin formula

encodePBLinAtLeastAdder :: PrimMonad m => Encoder m -> SAT.PBLinAtLeast -> m SAT.Lit
encodePBLinAtLeastAdder enc@(Encoder tseitin _) constr = do
  formula <- encodePBLinAtLeastAdder' enc constr
  Tseitin.encodeFormula tseitin formula

encodePBLinAtLeastAdder' :: PrimMonad m => Encoder m -> SAT.PBLinAtLeast -> m Tseitin.Formula
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

encodePBLinSumAdder :: forall m. PrimMonad m => Encoder m -> SAT.PBLinSum -> m [SAT.Lit]
encodePBLinSumAdder (Encoder tseitin _) lhs = do
  (buckets :: MutVar (PrimState m) (Seq (SQ.SeqQueue m SAT.Lit))) <- newMutVar Seq.empty
  let insert i x = do
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
              b <- Tseitin.encodeDisj tseitin [] -- False
              loop (i+1) (b : ret)
            1 -> do
              Just b <- SQ.dequeue q
              loop (i+1) (b : ret)
            2 -> do
              Just b1 <- SQ.dequeue q
              Just b2 <- SQ.dequeue q
              s <- encodeHASum tseitin b1 b2
              c <- encodeHACarry tseitin b1 b2
              insert (i+1) c
              loop (i+1) (s : ret)
            _ -> do
              Just b1 <- SQ.dequeue q
              Just b2 <- SQ.dequeue q
              Just b3 <- SQ.dequeue q
              s <- Tseitin.encodeFASum tseitin b1 b2 b3
              c <- Tseitin.encodeFACarry tseitin b1 b2 b3
              insert i s
              insert (i+1) c
              loop i ret
  loop 0 []

encodeHASum :: PrimMonad m => Tseitin.Encoder m -> SAT.Lit -> SAT.Lit -> m SAT.Lit
encodeHASum = Tseitin.encodeXOR

encodeHACarry :: PrimMonad m => Tseitin.Encoder m -> SAT.Lit -> SAT.Lit -> m SAT.Lit
encodeHACarry enc a b = Tseitin.encodeConj enc [a,b]

-- -----------------------------------------------------------------------

