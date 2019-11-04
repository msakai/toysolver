{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Encoder.PBNLC
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ExistentialQuantification, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses)
-- 
-----------------------------------------------------------------------------
module ToySolver.SAT.Encoder.PBNLC
  (
  -- * The encoder type
    Encoder
  , newEncoder
  , getTseitinEncoder

  -- * Adding constraints
  , addPBNLAtLeast
  , addPBNLAtMost  
  , addPBNLExactly
  , addPBNLAtLeastSoft
  , addPBNLAtMostSoft
  , addPBNLExactlySoft

  -- * Linearization
  , linearizePBSum
  , linearizePBSumWithPolarity
  ) where

import Control.Monad.Primitive
import ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import ToySolver.Internal.Util (revForM)

data Encoder m
  = forall a. SAT.AddPBLin m a => Encoder
  { encBase    :: a
  , encTseitin :: Tseitin.Encoder m
  }

instance Monad m => SAT.NewVar m (Encoder m) where
  newVar Encoder{ encBase = a }   = SAT.newVar a
  newVars Encoder{ encBase = a }  = SAT.newVars a
  newVars_ Encoder{ encBase = a } = SAT.newVars_ a

instance Monad m => SAT.AddClause m (Encoder m) where
  addClause Encoder{ encBase = a } = SAT.addClause a

instance Monad m => SAT.AddCardinality m (Encoder m) where
  addAtLeast Encoder{ encBase = a } = SAT.addAtLeast a
  addAtMost  Encoder{ encBase = a } = SAT.addAtMost a
  addExactly Encoder{ encBase = a } = SAT.addExactly a

instance Monad m => SAT.AddPBLin m (Encoder m) where
  addPBAtLeast Encoder{ encBase = a } = SAT.addPBAtLeast a
  addPBAtMost  Encoder{ encBase = a } = SAT.addPBAtMost a
  addPBExactly Encoder{ encBase = a } = SAT.addPBExactly a
  addPBAtLeastSoft Encoder{ encBase = a } = SAT.addPBAtLeastSoft a
  addPBAtMostSoft  Encoder{ encBase = a } = SAT.addPBAtMostSoft a
  addPBExactlySoft Encoder{ encBase = a } = SAT.addPBExactlySoft a

newEncoder :: (SAT.AddPBLin m a) => a -> Tseitin.Encoder m -> m (Encoder m)
newEncoder a tseitin = return $ Encoder a tseitin

getTseitinEncoder :: Encoder m -> Tseitin.Encoder m
getTseitinEncoder Encoder{ encTseitin = tseitin } = tseitin

instance PrimMonad m => SAT.AddPBNL m (Encoder m) where
  addPBNLAtLeast enc lhs rhs = do
    let c = sum [c | (c,[]) <- lhs]
    lhs' <- linearizePBSumWithPolarity enc Tseitin.polarityPos [(c,ls) | (c,ls) <- lhs, not (null ls)]
    SAT.addPBAtLeast enc lhs' (rhs - c)

  addPBNLAtMost enc lhs rhs =
    addPBNLAtLeast enc [(-c,ls) | (c,ls) <- lhs] (negate rhs)

  addPBNLExactly enc lhs rhs = do
    let c = sum [c | (c,[]) <- lhs]
    lhs' <- linearizePBSum enc [(c,ls) | (c,ls) <- lhs, not (null ls)]
    SAT.addPBExactly enc lhs' (rhs - c)

  addPBNLAtLeastSoft enc sel lhs rhs = do
    let c = sum [c | (c,[]) <- lhs]
    lhs' <- linearizePBSumWithPolarity enc Tseitin.polarityPos [(c,ls) | (c,ls) <- lhs, not (null ls)]
    SAT.addPBAtLeastSoft enc sel lhs' (rhs - c)

  addPBNLAtMostSoft enc sel lhs rhs =
    addPBNLAtLeastSoft enc sel [(negate c, lit) | (c,lit) <- lhs] (negate rhs)

  addPBNLExactlySoft enc sel lhs rhs = do
    let c = sum [c | (c,[]) <- lhs]
    lhs' <- linearizePBSum enc [(c,ls) | (c,ls) <- lhs, not (null ls)]
    SAT.addPBExactlySoft enc sel lhs' (rhs - c)

-- | Encode a non-linear 'PBSum' into a lienar 'PBLinSum'.
--
-- @linearizePBSum enc s@ is equivalent to @linearizePBSumWithPolarity enc polarityBoth@.
linearizePBSum
  :: PrimMonad m
  => Encoder m
  -> PBSum
  -> m PBLinSum
linearizePBSum enc = linearizePBSumWithPolarity enc Tseitin.polarityBoth

-- | Linearize a non-linear 'PBSum' into a lienar 'PBLinSum'.
--
-- The input 'PBSum' is assumed to occur only in specified polarity.
--
-- * If @'polarityPosOccurs' p@, the value of resulting 'PBLinSum' is /greater than/ or /equal to/ the value of original 'PBSum'.
--
-- * If @'polarityNegOccurs' p@, the value of resulting 'PBLinSum' is /lesser than/ or /equal to/ the value of original 'PBSum'.
-- 
linearizePBSumWithPolarity
  :: PrimMonad m
  => Encoder m
  -> Tseitin.Polarity -- polarity /p/
  -> PBSum
  -> m PBLinSum
linearizePBSumWithPolarity Encoder{ encTseitin = tseitin } p xs =
  revForM xs $ \(c,ls) -> do
    l <- if c > 0 then
           Tseitin.encodeConjWithPolarity tseitin p ls
         else
           Tseitin.encodeConjWithPolarity tseitin (Tseitin.negatePolarity p) ls
    return (c,l)
