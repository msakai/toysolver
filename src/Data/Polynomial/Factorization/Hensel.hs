{-# LANGUAGE ScopedTypeVariables, BangPatterns, TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Polynomial.Factorization.Hensel
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, BangPatterns, TemplateHaskell)
--
-- References:
--
-- * <http://www.math.kobe-u.ac.jp/Asir/ca.pdf>
-- 
-- * <http://www14.in.tum.de/konferenzen/Jass07/courses/1/Bulwahn/Buhlwahn_Paper.pdf>
--
-----------------------------------------------------------------------------
module Data.Polynomial.Factorization.Hensel
  ( hensel
  ) where

import Control.Exception (assert)
import Data.FiniteField
import Data.Polynomial (UPolynomial, X (..))
import qualified Data.Polynomial as P
import qualified TypeLevel.Number.Nat as TL

-- import Text.PrettyPrint.HughesPJClass

hensel :: forall p. TL.Nat p => UPolynomial Integer -> [UPolynomial (PrimeField p)] -> Integer -> [UPolynomial Integer]
hensel f fs1 k
  | k <= 0    = error "hensel; k <= 0"
  | otherwise = go 1 (map (P.mapCoeff Data.FiniteField.toInteger) fs1)
  where
    p :: Integer
    p = TL.toInt (undefined :: p)

    go :: Integer -> [UPolynomial Integer] -> [UPolynomial Integer]
    go !i fs
      | i==k      = assert (check i fs) $ fs
      | otherwise = assert (check i fs) $ go (i+1) (lift i fs)

    check :: Integer -> [UPolynomial Integer] -> Bool
    check k fs =
        and 
        [ P.mapCoeff (`mod` pk) f == P.mapCoeff (`mod` pk) (product fs)
        , fs1 == map (P.mapCoeff fromInteger) fs
        , and [P.deg fi1 == P.deg fik | (fi1, fik) <- zip (map (P.mapCoeff Data.FiniteField.toInteger) fs1) fs]
        ]
      where
        pk = p ^ k

    lift :: Integer -> [UPolynomial Integer] -> [UPolynomial Integer]
    lift k fs = fs'
      where
        pk  = p^k
        pk1 = p^(k+1)

        -- f ≡ product fs + p^k h  (mod p^(k+1))
        h :: UPolynomial Integer
        h = P.mapCoeff (\c -> (c `mod` pk1) `div` pk) h0
        h0 = (f - product fs)

        hs :: [UPolynomial (PrimeField p)]
        hs = prop_5_11 (map (P.mapCoeff fromInteger) fs) (P.mapCoeff fromInteger h)

        fs' :: [UPolynomial Integer]
        fs' = [ P.mapCoeff (`mod` pk1) (fi + P.constant pk * P.mapCoeff Data.FiniteField.toInteger hi)
              | (fi, hi) <- zip fs hs ]

-- http://www14.in.tum.de/konferenzen/Jass07/courses/1/Bulwahn/Buhlwahn_Paper.pdf
test_hensel :: Bool
test_hensel = and
  [ hensel f fs 2 == [x^(2::Int) + 5*x + 18, x + 5]
  , hensel f fs 3 == [x^(2::Int) + 105*x + 43, x + 30]
  , hensel f fs 4 == [x^(2::Int) + 605*x + 168, x + 30]
  ]
  where
    x :: forall k. (Eq k, Num k) => UPolynomial k
    x  = P.var X
    f :: UPolynomial Integer
    f  = x^(3::Int) + 10*x^(2::Int) - 432*x + 5040
    fs :: [UPolynomial $(primeField 5)]
    fs = [x^(2::Int)+3, x]

-- http://www.math.kobe-u.ac.jp/Asir/ca.pdf
prop_5_10 :: forall k. (Num k, Fractional k, Eq k) => [UPolynomial k] -> [UPolynomial k]
prop_5_10 fs = normalize (go fs)
  where
    check :: [UPolynomial k] -> [UPolynomial k] -> Bool
    check es fs = sum [ei * (product fs `P.div` fi) | (ei,fi) <- zip es fs] == 1

    go :: [UPolynomial k] -> [UPolynomial k]
    go [] = error "prop_5_10: empty list"
    go [fi] = assert (check [1] [fi]) [1]
    go fs@(fi : fs') = 
      case P.exgcd (product fs') fi of
        (g,ei,v) ->
           assert (g == 1) $
             let es' = go fs'
                 es  = ei : map (v*) es'
             in assert (check es fs) es

    normalize :: [UPolynomial k] -> [UPolynomial k]
    normalize es = assert (check es2 fs) es2
      where
        es2 = zipWith P.mod es fs

test_prop_5_10 :: Bool
test_prop_5_10 = sum [ei * (product fs `P.div` fi) | (ei,fi) <- zip es fs] == 1
  where
    x :: UPolynomial Rational
    x = P.var P.X
    fs = [x, x+1, x+2]
    es = prop_5_10 fs

-- http://www.math.kobe-u.ac.jp/Asir/ca.pdf
prop_5_11 :: forall k. (Num k, Fractional k, Eq k) => [UPolynomial k] -> UPolynomial k -> [UPolynomial k]
prop_5_11 fs g = normalize $ map (g*) $ prop_5_10 fs
  where
    check :: [UPolynomial k] -> [UPolynomial k] -> UPolynomial k -> Bool
    check es fs g = sum [ei * (product fs `P.div` fi) | (ei,fi) <- zip es fs] == g

    normalize :: [UPolynomial k] -> [UPolynomial k]
    normalize es = assert (check es2 fs g) es2
      where
        es2 = zipWith P.mod es fs

test_prop_5_11 :: Bool
test_prop_5_11 = sum [ei * (product fs `P.div` fi) | (ei,fi) <- zip es fs] == g
  where
    x :: UPolynomial Rational
    x = P.var P.X
    fs = [x, x+1, x+2]
    g  = x^(2::Int) + 1
    es = prop_5_11 fs g
