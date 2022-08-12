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
  , encodeAtLeastWithPolarity
  , getTseitinEncoder

    -- XXX
  , TotalizerDefinitions
  , getTotalizerDefinitions
  , evalTotalizerDefinitions

  -- * Polarity
  , Polarity (..)
  , negatePolarity
  , polarityPos
  , polarityNeg
  , polarityBoth
  , polarityNone
  ) where

import Control.Monad.Primitive
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import ToySolver.SAT.Encoder.Tseitin (Polarity (..), negatePolarity, polarityPos, polarityNeg, polarityBoth, polarityNone)
import ToySolver.SAT.Encoder.Cardinality.Internal.Naive
import ToySolver.SAT.Encoder.Cardinality.Internal.ParallelCounter
import ToySolver.SAT.Encoder.PB.Internal.BDD as BDD
import qualified ToySolver.SAT.Encoder.Cardinality.Internal.Totalizer as Totalizer

-- -------------------------------------------------------------------

-- XXX
data Encoder m = Encoder (Totalizer.Encoder m) Strategy

data Strategy
  = Naive
  | SequentialCounter
  | ParallelCounter
  | Totalizer
  deriving (Show, Eq, Ord, Enum, Bounded)
{-
"Sequential Counter" from "Towards an Optimal CNF Encoding of Boolean
Cardinality Constraints" is a special case of BDD-based encoding of
"Translating Pseudo-Boolean Constraints into SAT" (using the fact C→B
to represent ite(A,B,C) as (A∧B)∨C instead of (A∧B)∨(¬A∧C))?

http://www.carstensinz.de/papers/CP-2005.pdf
http://www.st.ewi.tudelft.nl/jsat/content/volume2/JSAT2_1_Een.pdf
-}

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

getTseitinEncoder :: Encoder m -> Tseitin.Encoder m
getTseitinEncoder (Encoder (Totalizer.Encoder tseitin _) _) = tseitin

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
          SequentialCounter -> BDD.addPBLinAtLeastBDD tseitin ([(1,l) | l <- lhs], fromIntegral rhs)
          Totalizer -> Totalizer.addAtLeast base (lhs,rhs)

encodeAtLeast :: PrimMonad m => Encoder m -> SAT.AtLeast -> m SAT.Lit
encodeAtLeast enc = encodeAtLeastWithPolarity enc polarityBoth

encodeAtLeastWithPolarity :: PrimMonad m => Encoder m -> Polarity -> SAT.AtLeast -> m SAT.Lit
encodeAtLeastWithPolarity (Encoder base@(Totalizer.Encoder tseitin _) strategy) polarity =
  case strategy of
    Naive -> encodeAtLeastWithPolarityNaive tseitin polarity
    ParallelCounter -> encodeAtLeastWithPolarityParallelCounter tseitin polarity
    SequentialCounter -> \(lhs,rhs) -> BDD.encodePBLinAtLeastWithPolarityBDD tseitin polarity ([(1,l) | l <- lhs], fromIntegral rhs)
    Totalizer -> Totalizer.encodeAtLeastWithPolarity base polarity
