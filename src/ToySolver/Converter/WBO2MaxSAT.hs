{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.WBO2MaxSAT
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (FlexibleContexts, MultiParamTypeClasses)
--
-----------------------------------------------------------------------------
module ToySolver.Converter.WBO2MaxSAT (convert) where

import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Data.Array.IArray
import qualified Data.Foldable as F
import Data.Monoid
import qualified Data.Sequence as Seq
import qualified Data.PseudoBoolean as PBFile

import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.Encoder.PB as PB
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC
import ToySolver.SAT.Store.CNF
import qualified ToySolver.Text.WCNF as WCNF
import qualified ToySolver.Text.CNF as CNF

convert :: PBFile.SoftFormula -> (WCNF.WCNF, SAT.Model -> SAT.Model, SAT.Model -> SAT.Model)
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
  let cs = softClauses <> Seq.fromList [(top, clause) | clause <- CNF.clauses cnf]
  let wcnf = WCNF.WCNF
             { WCNF.numVars = CNF.numVars cnf
             , WCNF.numClauses = Seq.length cs
             , WCNF.topCost = top
             , WCNF.clauses = F.toList cs
             }

  defs <- Tseitin.getDefinitions tseitin
  let extendModel :: SAT.Model -> SAT.Model
      extendModel m = array (1, CNF.numVars cnf) (assocs a)
        where
          -- Use BOXED array to tie the knot
          a :: Array SAT.Var Bool
          a = array (1, CNF.numVars cnf) $
                assocs m ++ [(v, Tseitin.evalFormula a phi) | (v, phi) <- defs]

  return (wcnf, extendModel, SAT.restrictModel (PBFile.wboNumVars formula))

-- -----------------------------------------------------------------------------
