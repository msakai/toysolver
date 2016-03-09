{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Store.PB
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (FlexibleContexts, MultiParamTypeClasses)
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Store.PB
  ( PBStore
  , newPBStore
  , getPBFormula
  ) where

import Control.Monad.ST
import Data.Foldable (toList)
import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import Data.STRef
import qualified Data.PseudoBoolean as PBFile
import qualified ToySolver.SAT.Types as SAT

data PBStore s = PBStore (STRef s Int) (STRef s (Seq PBFile.Constraint))

instance SAT.NewVar (ST s) (PBStore s) where
  newVar (PBStore ref _) = do
    modifySTRef' ref (+1)
    readSTRef ref

instance SAT.AddClause (ST s) (PBStore s) where
  addClause enc clause = SAT.addPBNLAtLeast enc [(1,[l]) | l <- clause] 1

instance SAT.AddCardinality (ST s) (PBStore s) where
  addAtLeast enc lhs rhs = SAT.addPBNLAtLeast enc [(1,[l]) | l <- lhs] (fromIntegral rhs)

instance SAT.AddPBLin (ST s) (PBStore s) where
  addPBAtLeast enc lhs rhs = SAT.addPBNLAtLeast enc [(c,[l]) | (c,l) <- lhs] rhs
  addPBAtMost enc lhs rhs  = SAT.addPBNLAtMost enc  [(c,[l]) | (c,l) <- lhs] rhs
  addPBExactly enc lhs rhs = SAT.addPBNLExactly enc [(c,[l]) | (c,l) <- lhs] rhs

instance SAT.AddPBNL (ST s) (PBStore s) where
  addPBNLAtLeast (PBStore _ ref) lhs rhs = do
    modifySTRef ref (|> (lhs, PBFile.Ge, rhs))
  addPBNLExactly (PBStore _ ref) lhs rhs = do
    modifySTRef ref (|> (lhs, PBFile.Eq, rhs))

newPBStore :: ST s (PBStore s)
newPBStore = do
  ref1 <- newSTRef 0
  ref2 <- newSTRef Seq.empty
  return (PBStore ref1 ref2)

getPBFormula :: PBStore s -> ST s (PBFile.Formula)
getPBFormula (PBStore ref1 ref2) = do
  nv <- readSTRef ref1
  cs <- readSTRef ref2
  return $
    PBFile.Formula
    { PBFile.pbObjectiveFunction = Nothing
    , PBFile.pbConstraints = toList cs
    , PBFile.pbNumVars = nv
    , PBFile.pbNumConstraints = Seq.length cs
    }
