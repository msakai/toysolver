{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PBLinearization
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PBLinearization
  ( linearize
  , linearizeWBO
  , PBLinearizeInfo (..)
  ) where

import Control.Monad
import Control.Monad.ST
import Data.Array.Unboxed
import qualified Data.PseudoBoolean as PBFile

import ToySolver.Converter.Base
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC
import ToySolver.SAT.Store.PB

-- -----------------------------------------------------------------------------

-- same as PB2SATInfo
data PBLinearizeInfo = PBLinearizeInfo !Int !Int [(SAT.Var, Tseitin.Formula)]

instance Transformer PBLinearizeInfo where
  type Source PBLinearizeInfo = SAT.Model
  type Target PBLinearizeInfo = SAT.Model

instance ForwardTransformer PBLinearizeInfo where
  transformForward (PBLinearizeInfo _nv1 nv2 defs) m = array (1, nv2) (assocs a)
    where
      -- Use BOXED array to tie the knot
      a :: Array SAT.Var Bool
      a = array (1, nv2) $
            assocs m ++ [(v, Tseitin.evalFormula a phi) | (v, phi) <- defs]

instance BackwardTransformer PBLinearizeInfo where
  transformBackward (PBLinearizeInfo nv1 _nv2 _defs) = SAT.restrictModel nv1

linearize :: PBFile.Formula -> Bool -> (PBFile.Formula, PBLinearizeInfo)
linearize formula usePB = runST $ do
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
  defs <- Tseitin.getDefinitions tseitin
  return $
    ( formula'
      { PBFile.pbObjectiveFunction = obj'
      , PBFile.pbConstraints = cs' ++ PBFile.pbConstraints formula'
      , PBFile.pbNumConstraints = PBFile.pbNumConstraints formula + PBFile.pbNumConstraints formula'
      }
    , PBLinearizeInfo (PBFile.pbNumVars formula) (PBFile.pbNumVars formula') defs
    )

-- -----------------------------------------------------------------------------

linearizeWBO :: PBFile.SoftFormula -> Bool -> (PBFile.SoftFormula, PBLinearizeInfo)
linearizeWBO formula usePB = runST $ do
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
  defs <- Tseitin.getDefinitions tseitin
  return $
    ( PBFile.SoftFormula
      { PBFile.wboTopCost = PBFile.wboTopCost formula
      , PBFile.wboConstraints = cs' ++ [(Nothing, constr) | constr <- PBFile.pbConstraints formula']
      , PBFile.wboNumVars = PBFile.pbNumVars formula'
      , PBFile.wboNumConstraints = PBFile.wboNumConstraints formula + PBFile.pbNumConstraints formula'
      }
    , PBLinearizeInfo (PBFile.wboNumVars formula) (PBFile.pbNumVars formula') defs
    ) 

-- -----------------------------------------------------------------------------
