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
-- * <http://en.wikipedia.org/wiki/Berlekamp%27s_algorithm>
--
-- * Martin Kreuzer and Lorenzo Robbiano. Computational Commutative Algebra 1. Springer Verlag, 2000.
--
-----------------------------------------------------------------------------
module Data.Polynomial.Factorization.FiniteField
  ( factor
  , sqfree
  , berlekamp
  , basisOfBerlekampSubalgebra
  ) where

import Control.Exception (assert)
import Data.FiniteField
import Data.Function (on)
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Polynomial
import qualified Data.Polynomial.GBasis as GB

factor :: forall k. (Ord k, FiniteField k) => UPolynomial k -> [(UPolynomial k, Integer)]
factor f = do
  (g,n) <- sqfree f
  if deg g > 0
    then do
      h <- berlekamp g
      return (h,n)
    else do
      return (g,n)

-- | Square-free decomposition of univariate polynomials over a finite field.
sqfree :: forall k. (Eq k, FiniteField k) => UPolynomial k -> [(UPolynomial k, Integer)]
sqfree f
  | c == 1    = sqfree' f
  | otherwise = (constant c, 1) : sqfree' (mapCoeff (/c) f)
  where
    c = lc ucmp f

sqfree' :: forall k. (Eq k, FiniteField k) => UPolynomial k -> [(UPolynomial k, Integer)]
sqfree' 0 = []
sqfree' f
  | g == 0    = [(h, n*p) | (h,n) <- sqfree' (polyPthRoot f)]
  | otherwise = go 1 c0 w0 []
  where
    p = char (undefined :: k)
    g = deriv f X
    c0 = pgcd f g
    w0 = pdiv f c0
    go !i c w !result
      | w == 1    =
          if c == 1
          then result
          else result ++ [(h, n*p) | (h,n) <- sqfree' (polyPthRoot c)]
      | otherwise = go (i+1) c' w' result'
          where
            y  = pgcd w c
            z  = w `pdiv` y            
            c' = c `pdiv` y
            w' = y
            result' = [(z,i) | z /= 1] ++ result

ucmp :: MonomialOrder X
ucmp = grlex

polyPthRoot :: forall k. (Eq k, FiniteField k) => UPolynomial k -> UPolynomial k
polyPthRoot f = assert (deriv f X == 0) $
  fromTerms [(pthRoot c, g mm) | (c,mm) <- terms f]
  where
    p = char (undefined :: k)
    g mm = var X `mpow` (deg mm `div` p)

-- | Berlekamp algorithm for polynomial factorization.
--
-- Input polynomial is assumed to be monic and square-free.
berlekamp :: forall k. (Eq k, Ord k, FiniteField k) => UPolynomial k -> [UPolynomial k]
berlekamp f = go (Set.singleton f) basis
  where
    go :: Set (UPolynomial k) -> [UPolynomial k] -> [UPolynomial k]
    go _ [] = error $ "berlekamp: should not happen"
    go fs (b:bs)
      | Set.size fs == r = Set.toList fs
      | otherwise = go (Set.unions [func fi | fi <- Set.toList fs]) bs
        where
          func fi = Set.fromList $ hs2 ++ hs1
            where
              hs1 = [h | k <- allValues, let h = pgcd fi (b - constant k), deg h > 0]
              hs2 = if deg g > 0 then [g] else []
                where
                  g = fi `pdiv` product hs1
    basis = basisOfBerlekampSubalgebra f
    r     = length basis

basisOfBerlekampSubalgebra :: forall k. (Ord k, FiniteField k) => UPolynomial k -> [UPolynomial k]
basisOfBerlekampSubalgebra f =
  sortBy (flip compare `on` deg) $
    map (toMonic ucmp) $
      basis
  where
    q    = order (undefined :: k)
    d    = deg f
    x    = var X

    qs :: [UPolynomial k]
    qs = [(x^(q*i)) `pmod` f | i <- [0 .. d - 1]]

    gb :: [Polynomial k Int]
    gb = GB.basis grlex [p3 | (p3,_) <- terms p2]

    p1 :: Polynomial k Int
    p1 = sum [var i * (subst qi (\X -> var (-1)) - (var (-1) ^ i)) | (i, qi) <- zip [0..] qs]
    p2 :: UPolynomial (Polynomial k Int)
    p2 = toUPolynomialOf p1 (-1)

    es  = [(i, reduce grlex (var i) gb) | i <- [0 .. fromIntegral d - 1]]
    vs1 = [i           | (i, gi_def) <- es, gi_def == var i]
    vs2 = [(i, gi_def) | (i, gi_def) <- es, gi_def /= var i]

    basis :: [UPolynomial k]
    basis = [ x^i + sum [constant (eval (delta i) gj_def) * x^j | (j, gj_def) <- vs2] | i <- vs1 ]
      where
        delta i k
          | k==i      = 1
          | otherwise = 0
