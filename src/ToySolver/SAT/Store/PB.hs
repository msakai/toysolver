{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Store.PB
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Store.PB
  ( PBStore
  , newPBStore
  , getPBFormula
  ) where

import Control.Monad.Primitive
import Data.Foldable (toList)
import Data.Primitive.MutVar
import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import qualified Data.PseudoBoolean as PBFile
import qualified ToySolver.SAT.Types as SAT

data PBStore m = PBStore (MutVar (PrimState m) Int) (MutVar (PrimState m) (Seq PBFile.Constraint)) (MutVar (PrimState m) (Maybe PBFile.Sum))

instance PrimMonad m => SAT.NewVar m (PBStore m) where
  newVar (PBStore ref _ _) = do
    modifyMutVar' ref (+1)
    readMutVar ref

instance PrimMonad m => SAT.AddClause m (PBStore m) where
  addClause enc clause = SAT.addPBNLAtLeast enc [(1,[l]) | l <- clause] 1

instance PrimMonad m => SAT.AddCardinality m (PBStore m) where
  addAtLeast enc lhs rhs = SAT.addPBNLAtLeast enc [(1,[l]) | l <- lhs] (fromIntegral rhs)

instance PrimMonad m => SAT.AddPBLin m (PBStore m) where
  addPBAtLeast enc lhs rhs = SAT.addPBNLAtLeast enc [(c,[l]) | (c,l) <- lhs] rhs
  addPBAtMost enc lhs rhs  = SAT.addPBNLAtMost enc  [(c,[l]) | (c,l) <- lhs] rhs
  addPBExactly enc lhs rhs = SAT.addPBNLExactly enc [(c,[l]) | (c,l) <- lhs] rhs

instance PrimMonad m => SAT.AddPBNL m (PBStore m) where
  addPBNLAtLeast (PBStore _ ref _) lhs rhs = do
    let lhs' = [(c,ls) | (c,ls@(_:_)) <- lhs]
        rhs' = rhs - sum [c | (c,[]) <- lhs]
    modifyMutVar' ref (|> (lhs', PBFile.Ge, rhs'))
  addPBNLExactly (PBStore _ ref _) lhs rhs = do
    let lhs' = [(c,ls) | (c,ls@(_:_)) <- lhs]
        rhs' = rhs - sum [c | (c,[]) <- lhs]
    modifyMutVar' ref (|> (lhs', PBFile.Eq, rhs'))

instance PrimMonad m => SAT.SetPBLinObjective m (PBStore m) where
  setPBObjectiveFunction enc obj = SAT.setPBNLObjectiveFunction enc (fmap (\o -> [(c,[l]) | (c,l) <- o]) obj)

instance PrimMonad m => SAT.SetPBNLObjective m (PBStore m) where
  setPBNLObjectiveFunction (PBStore _ _ ref) obj = writeMutVar ref obj

newPBStore :: PrimMonad m => m (PBStore m)
newPBStore = do
  ref1 <- newMutVar 0
  ref2 <- newMutVar Seq.empty
  ref3 <- newMutVar Nothing
  return (PBStore ref1 ref2 ref3)

getPBFormula :: PrimMonad m => PBStore m -> m (PBFile.Formula)
getPBFormula (PBStore ref1 ref2 ref3) = do
  nv <- readMutVar ref1
  cs <- readMutVar ref2
  obj <- readMutVar ref3
  return $
    PBFile.Formula
    { PBFile.pbObjectiveFunction = obj
    , PBFile.pbConstraints = toList cs
    , PBFile.pbNumVars = nv
    , PBFile.pbNumConstraints = Seq.length cs
    }
