{-# LANGUAGE BangPatterns, TypeSynonymInstances, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.Polynomial.Factorization.SquareFree
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (BangPatterns, TypeSynonymInstances, FlexibleInstances)
--
-- References:
--
-- * <http://www.math.kobe-u.ac.jp/Asir/ca.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.Data.Polynomial.Factorization.SquareFree
  ( sqfreeChar0
  ) where

import Control.Exception
import Data.Ratio

import ToySolver.Data.Polynomial.Base (UPolynomial, X (..))
import qualified ToySolver.Data.Polynomial.Base as P

-- | Square-free decomposition of univariate polynomials over a field of characteristic 0.
sqfreeChar0 :: (Eq k, Fractional k) => UPolynomial k -> [(UPolynomial k, Integer)]
sqfreeChar0 0 = []
sqfreeChar0 p = assert (product [q^m | (q,m) <- result] == p) $ result
  where
    result = go p (p `P.div` P.gcd p (P.deriv p X)) 0 []
    go p flat !m result
      | P.deg flat <= 0 = [(p,1) | p /= 1] ++ reverse result
      | otherwise     = go p' flat' m' ((flat `P.div` flat', m') : result)
          where
            (p',n) = f p flat
            flat'  = P.gcd p' flat
            m' = m + n

f :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> (UPolynomial k, Integer)
f p1 p2 = assert (p1 == p2 ^ m * q) $ result
  where
    result@(q, m) = go 0 p1
    go !m p =
      case p `P.divMod` p2 of
        (q, 0) -> go (m+1) q
        _ -> (p, m)


instance P.SQFree (UPolynomial Rational) where
  sqfree = sqfreeChar0

instance P.SQFree (UPolynomial Integer) where
  sqfree 0 = [(0,1)]
  sqfree f = go 1 [] (P.sqfree (P.mapCoeff fromIntegral f))
    where
      go !u ys [] =
        assert (denominator u == 1) $
          [(P.constant (numerator u), 1) | u /= 1] ++ ys
      go !u ys ((g,n):xs)
        | P.deg g <= 0 = go (u * P.coeff P.mone g) ys xs
        | otherwise    = go (u * (P.cont g)^n) ((P.mapCoeff numerator (P.pp g), n) : ys) xs
