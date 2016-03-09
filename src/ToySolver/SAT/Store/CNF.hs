{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Store.CNF
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (FlexibleContexts, MultiParamTypeClasses)
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Store.CNF
  ( CNFStore
  , newCNFStore
  , getCNFFormula
  ) where

import Control.Monad.ST
import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import Data.STRef
import qualified ToySolver.SAT.Types as SAT

data CNFStore s = CNFStore (STRef s Int) (STRef s (Seq SAT.Clause))

instance SAT.NewVar (ST s) (CNFStore s) where
  newVar (CNFStore ref _) = do
    modifySTRef' ref (+1)
    readSTRef ref

instance SAT.AddClause (ST s) (CNFStore s) where
  addClause (CNFStore _ ref) clause =
    case SAT.normalizeClause clause of
      Just clause' -> modifySTRef ref (|> clause')
      Nothing -> return ()

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
