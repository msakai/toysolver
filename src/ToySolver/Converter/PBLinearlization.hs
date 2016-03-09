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
import qualified Data.PseudoBoolean as PBFile

import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC
import ToySolver.SAT.Store.PB

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
