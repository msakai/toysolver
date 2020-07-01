{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.SAT2KSAT
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.SAT2KSAT
  ( sat2ksat
  , SAT2KSATInfo (..)
  ) where

import Control.Monad
import Control.Monad.ST
import Data.Array.MArray
import Data.Array.ST
import Data.Foldable (toList)
import Data.Sequence ((<|), (|>))
import qualified Data.Sequence as Seq
import Data.STRef

import ToySolver.Converter.Base
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.SAT.Types as SAT
import ToySolver.SAT.Store.CNF


sat2ksat :: Int -> CNF.CNF -> (CNF.CNF, SAT2KSATInfo)
sat2ksat k _ | k < 3 = error "ToySolver.Converter.SAT2KSAT.sat2ksat: k must be >=3"
sat2ksat k cnf = runST $ do
  let nv1 = CNF.cnfNumVars cnf
  db <- newCNFStore
  defsRef <- newSTRef Seq.empty
  SAT.newVars_ db nv1
  forM_ (CNF.cnfClauses cnf) $ \clause -> do
    let loop lits = do
          if Seq.length lits <= k then
            SAT.addClause db (toList lits)
          else do
            v <- SAT.newVar db
            case Seq.splitAt (k-1) lits of
              (lits1, lits2) -> do
                SAT.addClause db (toList (lits1 |> (-v)))
                modifySTRef' defsRef (|> (v, toList lits1))
                loop (v <| lits2)
    loop $ Seq.fromList $ SAT.unpackClause clause
  cnf2 <- getCNFFormula db
  defs <- readSTRef defsRef
  return (cnf2, SAT2KSATInfo nv1 (CNF.cnfNumVars cnf2) defs)


data SAT2KSATInfo = SAT2KSATInfo !Int !Int (Seq.Seq (SAT.Var, [SAT.Lit]))
  deriving (Eq, Show, Read)

instance Transformer SAT2KSATInfo where
  type Source SAT2KSATInfo = SAT.Model
  type Target SAT2KSATInfo = SAT.Model

instance ForwardTransformer SAT2KSATInfo where
  transformForward (SAT2KSATInfo nv1 nv2 defs) m = runSTUArray $ do
    m2 <- newArray_ (1,nv2)
    forM_ [1..nv1] $ \v -> do
      writeArray m2 v (SAT.evalVar m v)
    forM_ (toList defs) $ \(v, clause) -> do
      let f lit =
            if lit > 0 then
              readArray m2 lit
            else
              liftM not (readArray m2 (- lit))
      val <- liftM or (mapM f clause)
      writeArray m2 v val
    return m2

instance BackwardTransformer SAT2KSATInfo where
  transformBackward (SAT2KSATInfo nv1 _nv2 _defs) = SAT.restrictModel nv1

-- -----------------------------------------------------------------------------
