{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.Polynomial.Factorization.Hensel.Internal
-- Copyright   :  (c) Masahiro Sakai 2013-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, BangPatterns)
--
-- References:
--
-- * <http://www.math.kobe-u.ac.jp/Asir/ca.pdf>
-- 
-- * <http://www14.in.tum.de/konferenzen/Jass07/courses/1/Bulwahn/Buhlwahn_Paper.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.Data.Polynomial.Factorization.Hensel.Internal
  ( hensel
  , cabook_proposition_5_10
  , cabook_proposition_5_11
  ) where

import Control.Exception (assert)
import Data.FiniteField
import qualified TypeLevel.Number.Nat as TL

import ToySolver.Data.Polynomial.Base (UPolynomial)
import qualified ToySolver.Data.Polynomial.Base as P

-- import Text.PrettyPrint.HughesPJClass

hensel :: forall p. TL.Nat p => UPolynomial Integer -> [UPolynomial (PrimeField p)] -> Integer -> [UPolynomial Integer]
hensel f fs1 k
  | k <= 0    = error "ToySolver.Data.Polynomial.Factorization.Hensel.hensel: k <= 0"
  | otherwise = assert precondition $ go 1 (map (P.mapCoeff Data.FiniteField.toInteger) fs1)
  where
    precondition =
      P.mapCoeff fromInteger f == product fs1 && 
      P.deg f == P.deg (product fs1)

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
        , and [P.deg fi1 == P.deg fik | (fi1, fik) <- zip fs1 fs]
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
        h = P.mapCoeff (\c -> (c `mod` pk1) `div` pk) (f - product fs)

        hs :: [UPolynomial (PrimeField p)]
        hs = cabook_proposition_5_11 (map (P.mapCoeff fromInteger) fs) (P.mapCoeff fromInteger h)

        fs' :: [UPolynomial Integer]
        fs' = [ P.mapCoeff (`mod` pk1) (fi + P.constant pk * P.mapCoeff Data.FiniteField.toInteger hi)
              | (fi, hi) <- zip fs hs ]

-- http://www.math.kobe-u.ac.jp/Asir/ca.pdf
cabook_proposition_5_10
  :: forall k. (Num k, Fractional k, Eq k)
  => [UPolynomial k] -> [UPolynomial k]
cabook_proposition_5_10 fs = normalize (go fs)
  where
    check :: [UPolynomial k] -> [UPolynomial k] -> Bool
    check es fs = sum [ei * (product fs `P.div` fi) | (ei,fi) <- zip es fs] == 1

    go :: [UPolynomial k] -> [UPolynomial k]
    go [] = error "cabook_proposition_5_10: empty list"
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

-- http://www.math.kobe-u.ac.jp/Asir/ca.pdf
cabook_proposition_5_11
  :: forall k. (Fractional k, Ord k)
  => [UPolynomial k] -> UPolynomial k -> [UPolynomial k]
cabook_proposition_5_11 fs g =
  assert (P.deg g <= P.deg (product fs)) $
  assert (P.deg c <= 0) $
  assert (check es2 fs g) $
    es2
  where
    es  = map (g*) $ cabook_proposition_5_10 fs
    c   = sum [ei `P.div` fi | (ei,fi) <- zip es fs]
    es2 = case zipWith P.mod es fs of
            e2' : es2' -> e2' + c * head fs : es2'          

    check :: [UPolynomial k] -> [UPolynomial k] -> UPolynomial k -> Bool
    check es fs g =
      sum [ei * (product fs `P.div` fi) | (ei,fi) <- zip es fs] == g &&
      and [P.deg ei <= P.deg fi | (ei,fi) <- zip es fs]