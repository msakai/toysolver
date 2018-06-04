{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.WBO2MaxSAT
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.WBO2MaxSAT
  ( convert
  , WBO2MaxSATInfo (..)
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Data.Array.IArray
import qualified Data.Foldable as F
import Data.Monoid
import qualified Data.Sequence as Seq
import qualified Data.PseudoBoolean as PBFile

import ToySolver.Converter.Base
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.Encoder.PB as PB
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC
import ToySolver.SAT.Store.CNF
import qualified ToySolver.Text.CNF as CNF

convert :: PBFile.SoftFormula -> (CNF.WCNF, WBO2MaxSATInfo)
convert formula = runST $ do
  db <- newCNFStore
  SAT.newVars_ db (PBFile.wboNumVars formula)
  tseitin <-  Tseitin.newEncoder db
  pb <- PB.newEncoder tseitin
  pbnlc <- PBNLC.newEncoder pb tseitin

  softClauses <- liftM mconcat $ forM (PBFile.wboConstraints formula) $ \(cost, (lhs,op,rhs)) -> do
    case cost of
      Nothing ->
        case op of
          PBFile.Ge -> SAT.addPBNLAtLeast pbnlc lhs rhs >> return mempty
          PBFile.Eq -> SAT.addPBNLExactly pbnlc lhs rhs >> return mempty
      Just c -> do
        case op of
          PBFile.Ge -> do
            lhs2 <- PBNLC.linearizePBSumWithPolarity pbnlc Tseitin.polarityPos lhs
            let (lhs3,rhs3) = SAT.normalizePBLinAtLeast (lhs2,rhs)
            if rhs3==1 && and [c==1 | (c,_) <- lhs3] then
              return $ Seq.singleton (c, SAT.packClause [l | (_,l) <- lhs3])
            else do
              lit <- PB.encodePBLinAtLeast pb (lhs3,rhs3)
              return $ Seq.singleton (c, SAT.packClause [lit])
          PBFile.Eq -> do
            lhs2 <- PBNLC.linearizePBSumWithPolarity pbnlc Tseitin.polarityBoth lhs
            lit1 <- PB.encodePBLinAtLeast pb (lhs2, rhs)
            lit2 <- PB.encodePBLinAtLeast pb ([(-c, l) | (c,l) <- lhs2], negate rhs)
            lit <- Tseitin.encodeConjWithPolarity tseitin Tseitin.polarityPos [lit1,lit2]
            return $ Seq.singleton (c, SAT.packClause [lit])

  case PBFile.wboTopCost formula of
    Nothing -> return ()
    Just top -> SAT.addPBNLAtMost pbnlc [(c, [-l | l <- SAT.unpackClause clause]) | (c,clause) <- F.toList softClauses] (top - 1)

  let top = F.sum (fst <$> softClauses) + 1
  cnf <- getCNFFormula db
  let cs = softClauses <> Seq.fromList [(top, clause) | clause <- CNF.cnfClauses cnf]
  let wcnf = CNF.WCNF
             { CNF.wcnfNumVars = CNF.cnfNumVars cnf
             , CNF.wcnfNumClauses = Seq.length cs
             , CNF.wcnfTopCost = top
             , CNF.wcnfClauses = F.toList cs
             }
  defs <- Tseitin.getDefinitions tseitin
  return (wcnf, WBO2MaxSATInfo (PBFile.wboNumVars formula) (CNF.cnfNumVars cnf) defs)

-- same as PB2SATInfo
data WBO2MaxSATInfo = WBO2MaxSATInfo !Int !Int [(SAT.Var, Tseitin.Formula)]

instance Transformer WBO2MaxSATInfo where
  type Source WBO2MaxSATInfo = SAT.Model
  type Target WBO2MaxSATInfo = SAT.Model

instance ForwardTransformer WBO2MaxSATInfo where
  transformForward (WBO2MaxSATInfo _nv1 nv2 defs) m = array (1, nv2) (assocs a)
    where
      -- Use BOXED array to tie the knot
      a :: Array SAT.Var Bool
      a = array (1, nv2) $
            assocs m ++ [(v, Tseitin.evalFormula a phi) | (v, phi) <- defs]

instance BackwardTransformer WBO2MaxSATInfo where
  transformBackward (WBO2MaxSATInfo nv1 _nv2 _defs) = SAT.restrictModel nv1

-- -----------------------------------------------------------------------------
