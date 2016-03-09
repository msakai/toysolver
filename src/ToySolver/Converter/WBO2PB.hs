{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.WBO2PB
-- Copyright   :  (c) Masahiro Sakai 2013,2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.WBO2PB (convert) where

import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Data.Array.IArray
import Data.STRef
import qualified ToySolver.SAT.Types as SAT
import ToySolver.SAT.Store.PB
import qualified Data.PseudoBoolean as PBFile

convert :: PBFile.SoftFormula -> (PBFile.Formula, SAT.Model -> SAT.Model, SAT.Model -> SAT.Model)
convert wbo = runST $ do
  let nv = PBFile.wboNumVars wbo
  db <- newPBStore
  SAT.newVars_ db nv

  objRef <- newSTRef []
  defsRef <- newSTRef []
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
                modifySTRef objRef (\obj -> (w,[]) : (-w,ls) : obj)
              [(-1,ls)] | rhs == 0 -> do
                -- -1*∧L ≥ 0 ⇔ (1 - ∧L) ≥ 1 ⇔ ￢∧L
                -- obj += w * ∧L
                modifySTRef objRef ((w,ls) :)
              _ | and [c==1 && length ls == 1 | (c,ls) <- lhs] && rhs == 1 -> do
                -- ∑L ≥ 1 ⇔ ∨L ⇔ ￢∧￢L
                -- obj += w * ∧￢L
                modifySTRef objRef ((w, [-l | (_,[l]) <- lhs]) :)
              _ -> do
                sel <- SAT.newVar db
                SAT.addPBNLAtLeastSoft db sel lhs rhs
                modifySTRef objRef ((w,[-sel]) :)
                modifySTRef defsRef ((sel,constr) :)
          PBFile.Eq -> do
            sel <- SAT.newVar db
            SAT.addPBNLExactlySoft db sel lhs rhs
            modifySTRef objRef ((w,[-sel]) :)
            modifySTRef defsRef ((sel,constr) :)
  obj <- reverse <$> readSTRef objRef
  defs <- reverse <$> readSTRef defsRef

  case PBFile.wboTopCost wbo of
    Nothing -> return ()
    Just t -> SAT.addPBNLAtMost db obj (t - 1)

  formula <- getPBFormula db

  let mforth :: SAT.Model -> SAT.Model
      mforth m = array (1, (PBFile.pbNumVars formula)) $ assocs m ++ [(v, evalPBConstraint m constr) | (v, constr) <- defs]

      mback :: SAT.Model -> SAT.Model
      mback = SAT.restrictModel nv

  return
    ( formula{ PBFile.pbObjectiveFunction = Just obj }
    , mforth
    , mback
    )

evalPBConstraint :: SAT.Model -> PBFile.Constraint -> Bool
evalPBConstraint m (lhs,op,rhs) = op' (SAT.evalPBSum m lhs) rhs
  where
    op' = case op of
            PBFile.Ge -> (>=)
            PBFile.Eq -> (==)
