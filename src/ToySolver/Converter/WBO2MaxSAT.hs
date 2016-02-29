{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.WBO2MaxSAT
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.WBO2MaxSAT (convert) where

import Control.Applicative
import Control.Monad
import Control.Monad.ST
import qualified Data.Foldable as F
import Data.Monoid
import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import qualified Data.PseudoBoolean as PBFile
import Data.STRef

import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.Encoder.PB as PB
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC
import qualified ToySolver.Text.MaxSAT as MaxSAT

convert :: PBFile.SoftFormula -> MaxSAT.WCNF
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
              return $ Seq.singleton (c, [l | (_,l) <- lhs3])
            else do
              lit <- PB.encodePBLinAtLeast pb (lhs3,rhs3)
              return $ Seq.singleton (c, [lit])
          PBFile.Eq -> do
            lhs2 <- PBNLC.linearizePBSumWithPolarity pbnlc Tseitin.polarityBoth lhs
            lit1 <- PB.encodePBLinAtLeast pb (lhs2, rhs)
            lit2 <- PB.encodePBLinAtLeast pb ([(-c, l) | (c,l) <- lhs2], negate rhs)
            lit <- Tseitin.encodeConjWithPolarity tseitin Tseitin.polarityPos [lit1,lit2]
            return $ Seq.singleton (c, [lit])

  case PBFile.wboTopCost formula of
    Nothing -> return ()
    Just top -> SAT.addPBNLAtMost pbnlc [(c, [-l | l <- clause]) | (c,clause) <- F.toList softClauses] (top - 1)

  let top = F.sum (fst <$> softClauses) + 1
  (nv, hardClauses) <- getCNFFormula db
  let cs = softClauses <> fmap (\clause -> (top, clause)) hardClauses
  return $
    MaxSAT.WCNF
    { MaxSAT.numVars = nv
    , MaxSAT.numClauses = Seq.length cs
    , MaxSAT.topCost = top
    , MaxSAT.clauses = F.toList cs
    }

-- -----------------------------------------------------------------------------

data CNFStore s = CNFStore (STRef s Int) (STRef s (Seq SAT.Clause))

instance SAT.NewVar (ST s) (CNFStore s) where
  newVar (CNFStore ref _) = do
    modifySTRef' ref (+1)
    readSTRef ref

instance SAT.AddClause (ST s) (CNFStore s) where
  addClause (CNFStore _ ref) clause = modifySTRef ref (|> clause)

newCNFStore :: ST s (CNFStore s)
newCNFStore = do
  ref1 <- newSTRef 0
  ref2 <- newSTRef Seq.empty
  return (CNFStore ref1 ref2)

getCNFFormula :: CNFStore s -> ST s (Int, Seq SAT.Clause)
getCNFFormula (CNFStore ref1 ref2) = do
  nv <- readSTRef ref1
  cs <- readSTRef ref2
  return (nv, cs)

-- -----------------------------------------------------------------------------
