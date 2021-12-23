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
  , encodePBLinAtLeastBDD
  , encodePBLinAtLeastBDD'
  ) where

import Control.Monad.State.Strict
import Control.Monad.Primitive
import Data.Ord
import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import ToySolver.Data.Boolean
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin

addPBLinAtLeastBDD :: PrimMonad m => Tseitin.Encoder m -> SAT.PBLinAtLeast -> m ()
addPBLinAtLeastBDD enc constr = do
  formula <- encodePBLinAtLeastBDD' enc constr
  Tseitin.addFormula enc formula

encodePBLinAtLeastBDD :: forall m. PrimMonad m => Tseitin.Encoder m -> SAT.PBLinAtLeast -> m SAT.Lit
encodePBLinAtLeastBDD enc constr = do
  formula <- encodePBLinAtLeastBDD' enc constr
  Tseitin.encodeFormula enc formula

encodePBLinAtLeastBDD' :: forall m. PrimMonad m => Tseitin.Encoder m -> SAT.PBLinAtLeast -> m Tseitin.Formula
encodePBLinAtLeastBDD' _enc (lhs,rhs) = do
  let lhs' = sortBy (flip (comparing fst)) lhs
  flip evalStateT Map.empty $ do
    let f :: SAT.PBLinSum -> Integer -> Integer -> StateT (Map (SAT.PBLinSum, Integer) Tseitin.Formula) m Tseitin.Formula
        f xs rhs slack
          | rhs <= 0  = return true
          | slack < 0 = return false
          | otherwise = do
              m <- get
              case Map.lookup (xs,rhs) m of
                Just formula -> return formula
                Nothing -> do
                  case xs of
                    [] -> error "encodePBLinAtLeastBDD: should not happen"
                    [(_,l)] -> return $ Tseitin.Atom l
                    (c,l) : xs' -> do
                      thenFormula <- f xs' (rhs - c) slack
                      let f2 = Tseitin.Atom l .&&. thenFormula
                      f3 <- if c > slack then
                              return f2
                            else do
                              elseFormula <- f xs' rhs (slack - c)
                              return $ f2 .||. elseFormula
                      modify (Map.insert (xs,rhs) f3)
                      return f3
    f lhs' rhs (sum [c | (c,_) <- lhs'] - rhs)
