{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Encoder.PB.Internal.BDD
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
module ToySolver.SAT.Encoder.PB.Internal.BDD
  ( addPBLinAtLeastBDD
  , encodePBLinAtLeastWithPolarityBDD
  ) where

import Control.Monad.State.Strict
import Control.Monad.Primitive
import Data.Ord
import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin

addPBLinAtLeastBDD :: PrimMonad m => Tseitin.Encoder m -> SAT.PBLinAtLeast -> m ()
addPBLinAtLeastBDD enc constr = do
  l <- encodePBLinAtLeastWithPolarityBDD enc Tseitin.polarityPos constr
  SAT.addClause enc [l]

encodePBLinAtLeastWithPolarityBDD :: forall m. PrimMonad m => Tseitin.Encoder m -> Tseitin.Polarity -> SAT.PBLinAtLeast -> m SAT.Lit
encodePBLinAtLeastWithPolarityBDD enc polarity (lhs,rhs) = do
  let lhs' = sortBy (flip (comparing fst)) lhs
  flip evalStateT Map.empty $ do
    let f :: SAT.PBLinSum -> Integer -> Integer -> StateT (Map (SAT.PBLinSum, Integer) SAT.Lit) m SAT.Lit
        f xs rhs slack
          | rhs <= 0  = lift $ Tseitin.encodeConjWithPolarity enc polarity [] -- true
          | slack < 0 = lift $ Tseitin.encodeDisjWithPolarity enc polarity [] -- false
          | otherwise = do
              m <- get
              case Map.lookup (xs,rhs) m of
                Just l -> return l
                Nothing -> do
                  case xs of
                    [] -> error "encodePBLinAtLeastBDD: should not happen"
                    [(_,l)] -> return l
                    (c,l) : xs' -> do
                      thenLit <- f xs' (rhs - c) slack
                      l2 <- lift $ Tseitin.encodeConjWithPolarity enc polarity [l, thenLit]
                      l3 <- if c > slack then
                              return l2
                            else do
                              elseLit <- f xs' rhs (slack - c)
                              lift $ Tseitin.encodeDisjWithPolarity enc polarity [l2, elseLit]
                      modify (Map.insert (xs,rhs) l3)
                      return l3
    f lhs' rhs (sum [c | (c,_) <- lhs'] - rhs)
