{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.WBO2PB
-- Copyright   :  (c) Masahiro Sakai 2013,2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.WBO2PB
  ( convert
  , WBO2PBInfo (..)
  , addWBO
  ) where

import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Data.Array.IArray
import Data.Primitive.MutVar
import qualified ToySolver.SAT.Types as SAT
import ToySolver.SAT.Store.PB
import ToySolver.Converter.Base
import qualified Data.PseudoBoolean as PBFile

convert :: PBFile.SoftFormula -> (PBFile.Formula, WBO2PBInfo)
convert wbo = runST $ do
  let nv = PBFile.wboNumVars wbo
  db <- newPBStore
  (obj, defs) <- addWBO db wbo 
  formula <- getPBFormula db
  return
    ( formula{ PBFile.pbObjectiveFunction = Just obj }
    , WBO2PBInfo nv (PBFile.pbNumVars formula) defs
    )

data WBO2PBInfo = WBO2PBInfo !Int !Int [(SAT.Var, PBFile.Constraint)]

instance Transformer WBO2PBInfo where
  type Source WBO2PBInfo = SAT.Model
  type Target WBO2PBInfo = SAT.Model

instance ForwardTransformer WBO2PBInfo where
  transformForward (WBO2PBInfo _nv1 nv2 defs) m =
    array (1, nv2) $ assocs m ++ [(v, SAT.evalPBConstraint m constr) | (v, constr) <- defs]

instance BackwardTransformer WBO2PBInfo where
  transformBackward (WBO2PBInfo nv1 _nv2 _defs) = SAT.restrictModel nv1

addWBO :: (PrimMonad m, SAT.AddPBNL m enc) => enc -> PBFile.SoftFormula -> m (SAT.PBSum, [(SAT.Var, PBFile.Constraint)])
addWBO db wbo = do
  SAT.newVars_ db $ PBFile.wboNumVars wbo

  objRef <- newMutVar []
  defsRef <- newMutVar []
  forM_ (PBFile.wboConstraints wbo) $ \(cost, constr@(lhs,op,rhs)) -> do
    case cost of
      Nothing -> do
        case op of
          PBFile.Ge -> SAT.addPBNLAtLeast db lhs rhs
          PBFile.Eq -> SAT.addPBNLExactly db lhs rhs
      Just w -> do
        case op of
          PBFile.Ge -> do
            case lhs of
              [(1,ls)] | rhs == 1 -> do
                -- ∧L ≥ 1 ⇔ ∧L
                -- obj += w * (1 - ∧L)
                modifyMutVar objRef (\obj -> (w,[]) : (-w,ls) : obj)
              [(-1,ls)] | rhs == 0 -> do
                -- -1*∧L ≥ 0 ⇔ (1 - ∧L) ≥ 1 ⇔ ￢∧L
                -- obj += w * ∧L
                modifyMutVar objRef ((w,ls) :)
              _ | and [c==1 && length ls == 1 | (c,ls) <- lhs] && rhs == 1 -> do
                -- ∑L ≥ 1 ⇔ ∨L ⇔ ￢∧￢L
                -- obj += w * ∧￢L
                modifyMutVar objRef ((w, [-l | (_,[l]) <- lhs]) :)
              _ -> do
                sel <- SAT.newVar db
                SAT.addPBNLAtLeastSoft db sel lhs rhs
                modifyMutVar objRef ((w,[-sel]) :)
                modifyMutVar defsRef ((sel,constr) :)
          PBFile.Eq -> do
            sel <- SAT.newVar db
            SAT.addPBNLExactlySoft db sel lhs rhs
            modifyMutVar objRef ((w,[-sel]) :)
            modifyMutVar defsRef ((sel,constr) :)
  obj <- liftM reverse $ readMutVar objRef
  defs <- liftM reverse $ readMutVar defsRef

  case PBFile.wboTopCost wbo of
    Nothing -> return ()
    Just t -> SAT.addPBNLAtMost db obj (t - 1)

  return (obj, defs)
