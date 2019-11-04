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
  ) where

import Control.Monad.Primitive
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import ToySolver.SAT.Encoder.Cardinality.Internal.Naive
import ToySolver.SAT.Encoder.Cardinality.Internal.ParallelCounter

-- -------------------------------------------------------------------

data Encoder m = Encoder (Tseitin.Encoder m) Strategy

data Strategy
  = Naive
  | ParallelCounter
  deriving (Show, Eq, Ord, Enum, Bounded)

newEncoder :: Monad m => Tseitin.Encoder m -> m (Encoder m)
newEncoder tseitin = return $ Encoder tseitin ParallelCounter

newEncoderWithStrategy :: Monad m => Tseitin.Encoder m -> Strategy -> m (Encoder m)
newEncoderWithStrategy tseitin strategy = return (Encoder tseitin strategy)

-- getTseitinEncoder :: Encoder m -> Tseitin.Encoder m
-- getTseitinEncoder (Encoder tseitin _) = tseitin

instance Monad m => SAT.NewVar m (Encoder m) where
  newVar   (Encoder tseitin _) = SAT.newVar tseitin
  newVars  (Encoder tseitin _) = SAT.newVars tseitin
  newVars_ (Encoder tseitin _) = SAT.newVars_ tseitin

instance Monad m => SAT.AddClause m (Encoder m) where
  addClause (Encoder tseitin _) = SAT.addClause tseitin

instance PrimMonad m => SAT.AddCardinality m (Encoder m) where
  addAtLeast (Encoder tseitin strategy) lhs rhs
    | rhs <= 0  = return ()
    | otherwise =
        case strategy of
          Naive -> addAtLeastNaive tseitin (lhs,rhs)
          ParallelCounter -> addAtLeastParallelCounter tseitin (lhs,rhs)

encodeAtLeast :: PrimMonad m => Encoder m -> SAT.AtLeast -> m SAT.Lit
encodeAtLeast (Encoder tseitin strategy) =
  case strategy of
    Naive -> encodeAtLeastNaive tseitin
    ParallelCounter -> encodeAtLeastParallelCounter tseitin
