{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Polynomial.Factorization.FiniteField
-- Copyright   :  (c) Masahiro Sakai 2012-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, BangPatterns)
--
-- Factoriation of polynomial over a finite field.
--
-- References:
--
-- * <http://en.wikipedia.org/wiki/Factorization_of_polynomials_over_a_finite_field_and_irreducibility_tests>
--
-----------------------------------------------------------------------------
module Data.Polynomial.Factorization.FiniteField
  ( sqfree
  ) where

import Control.Exception (assert)
import Data.FiniteField
import qualified Data.Map as Map
import Data.Polynomial

-- | Square-free decomposition of univariate polynomials over a finite field.
sqfree :: forall k. (Eq k, FiniteField k) => UPolynomial k -> [(UPolynomial k, Integer)]
sqfree f
  | c == 1    = sqfree' f
  | otherwise = (constant c, 1) : sqfree' (mapCoeff (/c) f)
  where
    (c,_) = leadingTerm grlex f

sqfree' :: forall k. (Eq k, FiniteField k) => UPolynomial k -> [(UPolynomial k, Integer)]
sqfree' 0 = []
sqfree' f
  | g == 0    = [(h, n*p) | (h,n) <- sqfree' (polyPthRoot f)]
  | otherwise = go 1 c0 w0 []
  where
    p = char (undefined :: k)
    g = deriv f X
    c0 = polyGCD f g
    w0 = polyDiv f c0
    go !i c w !result
      | w == 1    =
          if c == 1
          then result
          else result ++ [(h, n*p) | (h,n) <- sqfree' (polyPthRoot c)]
      | otherwise = go (i+1) c' w' result'
          where
            y  = polyGCD w c
            z  = w `polyDiv` y            
            c' = c `polyDiv` y
            w' = y
            result' = [(z,i) | z /= 1] ++ result

polyPthRoot :: forall k. (Eq k, FiniteField k) => UPolynomial k -> UPolynomial k
polyPthRoot f = assert (deriv f X == 0) $
  fromTerms [(pthRoot c, g mm) | (c,mm) <- terms f]
  where
    p = char (undefined :: k)
    g mm = mmFromList [(X, (Map.findWithDefault 0 X (mmToMap mm)) `div` p)]
