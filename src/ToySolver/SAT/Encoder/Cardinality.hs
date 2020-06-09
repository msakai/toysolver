{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Encoder.Cardinality
-- Copyright   :  (c) Masahiro Sakai 2019
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Encoder.Cardinality
  ( Encoder
  , Strategy (..)
  , newEncoder
  , newEncoderWithStrategy
  , encodeAtLeast

    -- XXX
  , TotalizerDefinitions
  , getTotalizerDefinitions
  , evalTotalizerDefinitions
  ) where

import Control.Monad.Primitive
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import ToySolver.SAT.Encoder.Cardinality.Internal.Naive
import ToySolver.SAT.Encoder.Cardinality.Internal.ParallelCounter
import qualified ToySolver.SAT.Encoder.Cardinality.Internal.Totalizer as Totalizer

-- -------------------------------------------------------------------

-- XXX
data Encoder m = Encoder (Totalizer.Encoder m) Strategy

data Strategy
  = Naive
  | ParallelCounter
  | Totalizer
  deriving (Show, Eq, Ord, Enum, Bounded)

newEncoder :: PrimMonad m => Tseitin.Encoder m -> m (Encoder m)
newEncoder tseitin = newEncoderWithStrategy tseitin ParallelCounter

newEncoderWithStrategy :: PrimMonad m => Tseitin.Encoder m -> Strategy -> m (Encoder m)
newEncoderWithStrategy tseitin strategy = do
  base <- Totalizer.newEncoder tseitin
  return $ Encoder base strategy

type TotalizerDefinitions = Totalizer.Definitions

getTotalizerDefinitions :: PrimMonad m => Encoder m -> m TotalizerDefinitions
getTotalizerDefinitions (Encoder base _) = Totalizer.getDefinitions base

evalTotalizerDefinitions :: SAT.IModel m => m -> TotalizerDefinitions -> [(SAT.Var, Bool)]
evalTotalizerDefinitions m defs = Totalizer.evalDefinitions m defs

-- getTseitinEncoder :: Encoder m -> Tseitin.Encoder m
-- getTseitinEncoder (Encoder tseitin _) = tseitin

instance Monad m => SAT.NewVar m (Encoder m) where
  newVar   (Encoder base _) = SAT.newVar base
  newVars  (Encoder base _) = SAT.newVars base
  newVars_ (Encoder base _) = SAT.newVars_ base

instance Monad m => SAT.AddClause m (Encoder m) where
  addClause (Encoder base _) = SAT.addClause base

instance PrimMonad m => SAT.AddCardinality m (Encoder m) where
  addAtLeast (Encoder base@(Totalizer.Encoder tseitin _) strategy) lhs rhs
    | rhs <= 0  = return ()
    | otherwise =
        case strategy of
          Naive -> addAtLeastNaive tseitin (lhs,rhs)
          ParallelCounter -> addAtLeastParallelCounter tseitin (lhs,rhs)
          Totalizer -> Totalizer.addAtLeast base (lhs,rhs)

encodeAtLeast :: PrimMonad m => Encoder m -> SAT.AtLeast -> m SAT.Lit
encodeAtLeast (Encoder base@(Totalizer.Encoder tseitin _) strategy) =
  case strategy of
    Naive -> encodeAtLeastNaive tseitin
    ParallelCounter -> encodeAtLeastParallelCounter tseitin
    Totalizer -> Totalizer.encodeAtLeast base
