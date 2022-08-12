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
  , encodeAtLeastWithPolarityNaive
  ) where

import Control.Monad.Primitive
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import ToySolver.SAT.Encoder.Tseitin (Polarity ())

addAtLeastNaive :: PrimMonad m => Tseitin.Encoder m -> SAT.AtLeast -> m ()
addAtLeastNaive enc (lhs,rhs) = do
  let n = length lhs
  if n < rhs then do
    SAT.addClause enc []
  else do
    mapM_ (SAT.addClause enc) (comb (n - rhs + 1) lhs)

encodeAtLeastWithPolarityNaive :: PrimMonad m => Tseitin.Encoder m -> Polarity -> SAT.AtLeast -> m SAT.Lit
encodeAtLeastWithPolarityNaive enc polarity (lhs,rhs) = do
  let n = length lhs
  if n < rhs then do
    Tseitin.encodeDisjWithPolarity enc polarity []
  else do
    ls <- mapM (Tseitin.encodeDisjWithPolarity enc polarity) (comb (n - rhs + 1) lhs)
    Tseitin.encodeConjWithPolarity enc polarity ls

comb :: Int -> [a] -> [[a]]
comb 0 _ = [[]]
comb _ [] = []
comb n (x:xs) = map (x:) (comb (n-1) xs) ++ comb n xs
