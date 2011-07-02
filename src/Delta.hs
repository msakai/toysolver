{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Delta
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Reference:
-- 
-- Bruno Dutertre, Leonardo de Moura.
-- A Fast Linear-Arithmetic Solver for DPLL(T).
-- Computer Aided Verification In Computer Aided Verification, Vol. 4144
-- (2006), pp. 81-94.
-- http://dx.doi.org/10.1007/11817963_11
-- http://www.csl.sri.com/users/demoura/papers/CAV06/index.html
--
-----------------------------------------------------------------------------

module Delta where

import Linear

-- | "Delta r k" denotes r + kδ for infinitesimal parameter δ.
data Delta r = Delta !r !r deriving (Ord, Eq, Show)

delta :: Num r => Delta r
delta = Delta 0 1

instance Num r => Linear r (Delta r) where
  Delta r1 k1 .+. Delta r2 k2 = Delta (r1+r2) (k1+k2)
  c .*. Delta r k = Delta (c*r) (c*k)
  lzero = Delta 0 0

floor', ceiling' :: (RealFrac r, Integral a) => Delta r -> a

floor' (Delta r k) = fromInteger $ if r2==r && k < 0 then i-1 else i
  where
    i = floor r
    r2 = fromInteger i

ceiling' (Delta r k) = fromInteger $ if r2==r && k > 0 then i+1 else i
  where
    i = ceiling r
    r2 = fromInteger i
