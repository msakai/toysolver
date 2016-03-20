{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.WBO2PB
-- Copyright   :  (c) Masahiro Sakai 2013,2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (MultiParamTypeClasses)
--
-----------------------------------------------------------------------------
module ToySolver.Converter.WBO2PB
  ( convert
  , addWBO
  ) where

import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Data.Array.IArray
import Data.Primitive.MutVar
import qualified ToySolver.SAT.Types as SAT
import ToySolver.SAT.Store.PB
import qualified Data.PseudoBoolean as PBFile

convert :: PBFile.SoftFormula -> (PBFile.Formula, SAT.Model -> SAT.Model, SAT.Model -> SAT.Model)
convert wbo = runST $ do
  let nv = PBFile.wboNumVars wbo
  db <- newPBStore
  (obj, defs) <- addWBO db wbo 
  formula <- getPBFormula db

  let mforth :: SAT.Model -> SAT.Model
      mforth m = array (1, PBFile.pbNumVars formula) $ assocs m ++ [(v, SAT.evalPBConstraint m constr) | (v, constr) <- defs]

      mback :: SAT.Model -> SAT.Model
      mback = SAT.restrictModel nv

  return
    ( formula{ PBFile.pbObjectiveFunction = Just obj }
    , mforth
    , mback
    )


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
