{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PBLinearlization
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PBLinearlization
  ( linearlize
  , linearlizeWBO
  ) where

import Control.Monad
import Control.Monad.ST
import Data.Foldable (toList)
import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import qualified Data.PseudoBoolean as PBFile
import Data.STRef

import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC

linearlize :: PBFile.Formula -> Bool -> PBFile.Formula
linearlize formula usePB = runST $ do
  db <- newPBStore
  SAT.newVars_ db (PBFile.pbNumVars formula)
  tseitin <-  Tseitin.newEncoderWithPBLin db
  Tseitin.setUsePB tseitin usePB
  pbnlc <- PBNLC.newEncoder db tseitin
  cs' <- forM (PBFile.pbConstraints formula) $ \(lhs,op,rhs) -> do
    let p = case op of
              PBFile.Ge -> Tseitin.polarityPos
              PBFile.Eq -> Tseitin.polarityBoth
    lhs' <- PBNLC.linearizePBSumWithPolarity pbnlc p lhs
    return ([(c,[l]) | (c,l) <- lhs'],op,rhs)
  obj' <-
    case PBFile.pbObjectiveFunction formula of
      Nothing -> return Nothing
      Just obj -> do
        obj' <- PBNLC.linearizePBSumWithPolarity pbnlc Tseitin.polarityNeg obj
        return $ Just [(c, [l]) | (c,l) <- obj']
  formula' <- getPBFormula db
  return $
    formula'
    { PBFile.pbObjectiveFunction = obj'
    , PBFile.pbConstraints = cs' ++ PBFile.pbConstraints formula'
    , PBFile.pbNumConstraints = PBFile.pbNumConstraints formula + PBFile.pbNumConstraints formula'
    }

linearlizeWBO :: PBFile.SoftFormula -> Bool -> PBFile.SoftFormula
linearlizeWBO formula usePB = runST $ do
  db <- newPBStore
  SAT.newVars_ db (PBFile.wboNumVars formula)
  tseitin <-  Tseitin.newEncoderWithPBLin db
  Tseitin.setUsePB tseitin usePB
  pbnlc <- PBNLC.newEncoder db tseitin
  cs' <- forM (PBFile.wboConstraints formula) $ \(cost,(lhs,op,rhs)) -> do
    let p = case op of
              PBFile.Ge -> Tseitin.polarityPos
              PBFile.Eq -> Tseitin.polarityBoth
    lhs' <- PBNLC.linearizePBSumWithPolarity pbnlc p lhs
    return (cost,([(c,[l]) | (c,l) <- lhs'],op,rhs))
  formula' <- getPBFormula db
  return $
    PBFile.SoftFormula
    { PBFile.wboTopCost = PBFile.wboTopCost formula
    , PBFile.wboConstraints = cs' ++ [(Nothing, constr) | constr <- PBFile.pbConstraints formula']
    , PBFile.wboNumVars = PBFile.pbNumVars formula'
    , PBFile.wboNumConstraints = PBFile.wboNumConstraints formula + PBFile.pbNumConstraints formula'
    }

-- -----------------------------------------------------------------------------

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

-- -----------------------------------------------------------------------------
