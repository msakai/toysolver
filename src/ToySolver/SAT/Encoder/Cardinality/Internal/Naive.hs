{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Encoder.Cardinality.Internal.Naive
-- Copyright   :  (c) Masahiro Sakai 2019
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Encoder.Cardinality.Internal.Naive
  ( addAtLeastNaive
  , encodeAtLeastNaive
  ) where

import Control.Monad.Primitive
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin

addAtLeastNaive :: PrimMonad m => Tseitin.Encoder m -> SAT.AtLeast -> m ()
addAtLeastNaive enc (lhs,rhs) = do
  let n = length lhs
  if n < rhs then do
    SAT.addClause enc []
  else do
    mapM_ (SAT.addClause enc) (comb (n - rhs + 1) lhs)

-- TODO: consider polarity
encodeAtLeastNaive :: PrimMonad m => Tseitin.Encoder m -> SAT.AtLeast -> m SAT.Lit
encodeAtLeastNaive enc (lhs,rhs) = do
  let n = length lhs
  if n < rhs then do
    Tseitin.encodeDisj enc []
  else do
    ls <- mapM (Tseitin.encodeDisj enc) (comb (n - rhs + 1) lhs)
    Tseitin.encodeConj enc ls

comb :: Int -> [a] -> [[a]]
comb 0 _ = [[]]
comb _ [] = []
comb n (x:xs) = map (x:) (comb (n-1) xs) ++ comb n xs
