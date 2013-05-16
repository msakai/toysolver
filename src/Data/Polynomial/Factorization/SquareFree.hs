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
import Data.Polynomial (UPolynomial, X (..))
import qualified Data.Polynomial as P

-- | Square-free decomposition of univariate polynomials over a field of characteristic 0.
sqfree :: (Eq k, Fractional k) => UPolynomial k -> [(UPolynomial k, Integer)]
sqfree 0 = []
sqfree p = assert (product [q^m | (q,m) <- result] == p) $ result
  where
    result = go p (p `P.pdiv` P.pgcd p (P.deriv p X)) 0 []
    go p flat !m result
      | P.deg flat <= 0 = [(p,1) | p /= 1] ++ reverse result
      | otherwise     = go p' flat' m' ((flat `P.pdiv` flat', m') : result)
          where
            (p',n) = f p flat
            flat'  = P.pgcd p' flat
            m' = m + n

f :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> (UPolynomial k, Integer)
f p1 p2 = assert (p1 == p2 ^ m * q) $ result
  where
    result@(q, m) = go 0 p1
    go !m p =
      case p `P.pdivMod` p2 of
        (q, 0) -> go (m+1) q
        _ -> (p, m)
