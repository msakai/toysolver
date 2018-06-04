{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PB2SAT
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PB2SAT
  ( convert
  , PB2SATInfo
  ) where

import Control.Monad
import Control.Monad.ST
import Data.Array.IArray
import qualified Data.PseudoBoolean as PBFile

import ToySolver.Converter.Base
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.Encoder.PB as PB
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC
import ToySolver.SAT.Store.CNF
import qualified ToySolver.Text.CNF as CNF

-- same as WBO2MaxSATInfo
data PB2SATInfo = PB2SATInfo !Int !Int [(SAT.Var, Tseitin.Formula)]

instance Transformer PB2SATInfo where
  type Source PB2SATInfo = SAT.Model
  type Target PB2SATInfo = SAT.Model

instance ForwardTransformer PB2SATInfo where
  transformForward (PB2SATInfo _nv1 nv2 defs) m = array (1, nv2) (assocs a)
    where
      -- Use BOXED array to tie the knot
      a :: Array SAT.Var Bool
      a = array (1, nv2) $
            assocs m ++ [(v, Tseitin.evalFormula a phi) | (v, phi) <- defs]

instance BackwardTransformer PB2SATInfo where
  transformBackward (PB2SATInfo nv1 _nv2 _defs) = SAT.restrictModel nv1

-- | Convert a pseudo boolean formula φ to a equisatisfiable CNF formula ψ
-- together with two functions f and g such that:
--
-- * if M ⊨ φ then f(M) ⊨ ψ
--
-- * if M ⊨ ψ then g(M) ⊨ φ
-- 
convert :: PBFile.Formula -> (CNF.CNF, PB2SATInfo)
convert formula = runST $ do
  db <- newCNFStore
  let nv1 = PBFile.pbNumVars formula
  SAT.newVars_ db nv1
  tseitin <-  Tseitin.newEncoder db
  pb <- PB.newEncoder tseitin
  pbnlc <- PBNLC.newEncoder pb tseitin
  forM_ (PBFile.pbConstraints formula) $ \(lhs,op,rhs) -> do
    case op of
      PBFile.Ge -> SAT.addPBNLAtLeast pbnlc lhs rhs
      PBFile.Eq -> SAT.addPBNLExactly pbnlc lhs rhs
  cnf <- getCNFFormula db
  defs <- Tseitin.getDefinitions tseitin
  return (cnf, PB2SATInfo nv1 (CNF.cnfNumVars cnf) defs)

-- -----------------------------------------------------------------------------
