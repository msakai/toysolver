{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Encoder.PB
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
module ToySolver.SAT.Encoder.PB
  ( Encoder
  , Strategy (..)
  , newEncoder
  , newEncoderWithStrategy
  , encodePBLinAtLeast
  ) where

import Control.Monad.Primitive
import Data.Default.Class
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import ToySolver.SAT.Encoder.PB.Internal.Adder (addPBLinAtLeastAdder, encodePBLinAtLeastAdder)
import ToySolver.SAT.Encoder.PB.Internal.BDD (addPBLinAtLeastBDD, encodePBLinAtLeastBDD)
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
addPBLinAtLeast' (Encoder tseitin strategy) =
  case strategy of
    Adder -> addPBLinAtLeastAdder tseitin
    Sorter -> addPBLinAtLeastSorter tseitin
    _ -> addPBLinAtLeastBDD tseitin

encodePBLinAtLeast' :: PrimMonad m => Encoder m -> SAT.PBLinAtLeast -> m SAT.Lit
encodePBLinAtLeast' (Encoder tseitin strategy) =
  case strategy of
    Adder -> encodePBLinAtLeastAdder tseitin
    Sorter -> encodePBLinAtLeastSorter tseitin
    _ -> encodePBLinAtLeastBDD tseitin

-- -----------------------------------------------------------------------

