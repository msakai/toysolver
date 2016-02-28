{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PB2SAT
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PB2SAT (convert) where

import Control.Monad
import Control.Monad.ST
import Data.Array.IArray
import Data.Foldable (toList)
import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import qualified Data.PseudoBoolean as PBFile
import Data.STRef
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS

import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.Encoder.PB as PB
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC

convert :: PBFile.Formula -> DIMACS.CNF
convert formula = runST $ do
  db <- newCNFStore
  SAT.newVars_ db (PBFile.pbNumVars formula)
  tseitin <-  Tseitin.newEncoder db
  pb <- PB.newEncoder tseitin
  pbnlc <- PBNLC.newEncoder pb tseitin
  forM_ (PBFile.pbConstraints formula) $ \(lhs,op,rhs) -> do
    case op of
      PBFile.Ge -> SAT.addPBNLAtLeast pbnlc lhs rhs
      PBFile.Eq -> SAT.addPBNLExactly pbnlc lhs rhs
  (nv, cs) <- getCNFFormula db
  return $
    DIMACS.CNF
    { DIMACS.numVars = nv
    , DIMACS.numClauses = Seq.length cs
    , DIMACS.clauses = [listArray (0, length c - 1) c | c <- toList cs]
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
