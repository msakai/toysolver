{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Store.CNF
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (FlexibleContexts, FlexibleInstances, MultiParamTypeClasses)
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Store.CNF
  ( CNFStore
  , newCNFStore
  , getCNFFormula
  ) where

import Control.Monad.Primitive
import qualified Data.Foldable as F
import Data.Primitive.MutVar
import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.Text.CNF as CNF

data CNFStore m = CNFStore (MutVar (PrimState m) Int) (MutVar (PrimState m) (Seq SAT.PackedClause))

instance PrimMonad m => SAT.NewVar m (CNFStore m) where
  newVar (CNFStore ref _) = do
    modifyMutVar' ref (+1)
    readMutVar ref

instance PrimMonad m => SAT.AddClause m (CNFStore m) where
  addClause (CNFStore _ ref) clause =
    case SAT.normalizeClause clause of
      Just clause' -> do
        let clause'' = SAT.packClause clause'
        seq clause'' $ modifyMutVar' ref (|> clause'')
      Nothing -> return ()

newCNFStore :: PrimMonad m => m (CNFStore m)
newCNFStore = do
  ref1 <- newMutVar 0
  ref2 <- newMutVar Seq.empty
  return (CNFStore ref1 ref2)

getCNFFormula :: PrimMonad m => CNFStore m -> m CNF.CNF
getCNFFormula (CNFStore ref1 ref2) = do
  nv <- readMutVar ref1
  cs <- readMutVar ref2
  return $
     CNF.CNF
     { CNF.numVars = nv
     , CNF.numClauses = Seq.length cs
     , CNF.clauses = F.toList cs
     }
