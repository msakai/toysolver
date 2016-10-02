{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PB2SAT
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (FlexibleContexts, MultiParamTypeClasses)
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PB2SAT (convert) where

import Control.Monad
import Control.Monad.ST
import Data.Array.IArray
import Data.Foldable (toList)
import qualified Data.Sequence as Seq
import qualified Data.PseudoBoolean as PBFile

import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.Encoder.PB as PB
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC
import ToySolver.SAT.Store.CNF
import qualified ToySolver.Text.CNF as CNF

-- | Convert a pseudo boolean formula φ to a equisatisfiable CNF formula ψ
-- together with two functions f and g such that:
--
-- * if M ⊨ φ then f(M) ⊨ ψ
--
-- * if M ⊨ ψ then g(M) ⊨ φ
-- 
convert :: PBFile.Formula -> (CNF.CNF, SAT.Model -> SAT.Model, SAT.Model -> SAT.Model)
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
  let extendModel :: SAT.Model -> SAT.Model
      extendModel m = array (1, CNF.numVars cnf) (assocs a)
        where
          -- Use BOXED array to tie the knot
          a :: Array SAT.Var Bool
          a = array (1, CNF.numVars cnf) $
                assocs m ++ [(v, Tseitin.evalFormula a phi) | (v, phi) <- defs]

  return (cnf, extendModel, SAT.restrictModel nv1)

-- -----------------------------------------------------------------------------
