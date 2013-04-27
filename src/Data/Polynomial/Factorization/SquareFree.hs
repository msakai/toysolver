{-# LANGUAGE BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Polynomial.Factorization.SquareFree
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (BangPatterns)
--
-- Square-free decomposition of univariate polynomials over a field of characteristic 0.
--
-- References:
--
-- * <http://www.math.kobe-u.ac.jp/Asir/ca.pdf>
--
-----------------------------------------------------------------------------
module Data.Polynomial.Factorization.SquareFree
  ( sqfree
  ) where

import Control.Exception
import Data.Polynomial

-- | Square-free decomposition of univariate polynomials over a field of characteristic 0.
sqfree :: (Eq k, Fractional k) => UPolynomial k -> [(UPolynomial k, Integer)]
sqfree 0 = []
sqfree p = assert (product [q^m | (q,m) <- result] == p) $ result
  where
    result = go p (p `polyDiv` polyGCD p (deriv p X)) 0 []
    go p flat !m result
      | deg flat <= 0 = [(p,1) | p /= 1] ++ reverse result
      | otherwise     = go p' flat' m' ((flat `polyDiv` flat', m') : result)
          where
            (p',n) = f p flat
            flat'  = polyGCD p' flat
            m' = m + n

f :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> (UPolynomial k, Integer)
f p1 p2 = assert (p1 == p2 ^ m * q) $ result
  where
    result@(q, m) = go 0 p1
    go !m p =
      case p `polyDivMod` p2 of
        (q, 0) -> go (m+1) q
        _ -> (p, m)
