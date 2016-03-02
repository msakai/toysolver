{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Encoder.PB
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses)
--
-- References:
--
-- * [ES06] N . Eéen and N. Sörensson. Translating Pseudo-Boolean
--   Constraints into SAT. JSAT 2:1–26, 2006.
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Encoder.PB
  ( Encoder
  , newEncoder
  , encodePBLinAtLeast
  ) where

import Control.Monad.Primitive
import Control.Monad.State.Strict
import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Ord
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin

newtype Encoder m = Encoder (Tseitin.Encoder m)

newEncoder :: Monad m => Tseitin.Encoder m -> m (Encoder m)
newEncoder tseitin = return (Encoder tseitin)

instance Monad m => SAT.NewVar m (Encoder m) where
  newVar   (Encoder a) = SAT.newVar a
  newVars  (Encoder a) = SAT.newVars a
  newVars_ (Encoder a) = SAT.newVars_ a

instance Monad m => SAT.AddClause m (Encoder m) where
  addClause (Encoder a) = SAT.addClause a

instance PrimMonad m => SAT.AddCardinality m (Encoder m) where
  addAtLeast enc lhs rhs = SAT.addPBAtLeast enc [(1, l) | l <- lhs] (fromIntegral rhs)

instance PrimMonad m => SAT.AddPBLin m (Encoder m) where
  addPBAtLeast enc lhs rhs = do
    let (lhs',rhs') = SAT.normalizePBLinAtLeast (lhs,rhs)
    if rhs' == 1 && and [c==1 | (c,_) <- lhs'] then
      SAT.addClause enc [l | (_,l) <- lhs']
    else do
      l <- encodePBLinAtLeast' enc (lhs',rhs')
      SAT.addClause enc [l]

encodePBLinAtLeast :: forall m. PrimMonad m => Encoder m -> SAT.PBLinAtLeast -> m SAT.Lit
encodePBLinAtLeast enc constr =
  encodePBLinAtLeast' enc $ SAT.normalizePBLinAtLeast constr

encodePBLinAtLeast' :: forall m. PrimMonad m => Encoder m -> SAT.PBLinAtLeast -> m SAT.Lit
encodePBLinAtLeast' (Encoder tseitin) (lhs,rhs) = do
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
