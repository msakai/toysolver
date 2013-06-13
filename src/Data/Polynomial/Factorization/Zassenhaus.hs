{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Polynomial.Factorization.Zassenhaus
-- Copyright   :  (c) Masahiro Sakai 2012-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (BangPatterns, ScopedTypeVariables)
--
-- Factoriation of integer-coefficient polynomial using Zassenhaus algorithm.
--
-- References:
--
-- * <http://www.math.kobe-u.ac.jp/Asir/ca.pdf>
--
-----------------------------------------------------------------------------
module Data.Polynomial.Factorization.Zassenhaus
  ( factor
  ) where

import Control.Monad
import Control.Monad.ST
import Control.Exception (assert)
import Data.List
import Data.Maybe
import Data.Numbers.Primes (primes)
import Data.Ratio
import Data.STRef

import Data.Polynomial.Base (UPolynomial, X (..))
import qualified Data.Polynomial.Base as P
import Data.Polynomial.Factorization.FiniteField ()
import Data.Polynomial.Factorization.SquareFree ()
import qualified Data.Polynomial.Factorization.Hensel as Hensel

import qualified TypeLevel.Number.Nat as TL
import Data.FiniteField
import Data.FiniteField.SomeNat (SomeNat (..))
import qualified Data.FiniteField.SomeNat as SomeNat

-- import Text.PrettyPrint.HughesPJClass

factor :: UPolynomial Integer -> [(UPolynomial Integer, Integer)]
factor f = [(h,n) | (g,n) <- P.sqfree f, h <- if P.deg g > 0 then zassenhaus g else return g]

zassenhaus :: UPolynomial Integer -> [UPolynomial Integer]
zassenhaus f = head $ do
  p <- primes
  maybeToList $ zassenhausWithP f p

zassenhausWithP :: UPolynomial Integer -> Integer -> Maybe [UPolynomial Integer]
zassenhausWithP f p =
  case SomeNat.fromInteger p of
    SomeNat (_ :: p) -> do
      let f_mod_p :: UPolynomial (PrimeField p)
          f_mod_p = P.mapCoeff fromInteger f
      guard $ P.deg f == P.deg f_mod_p -- 主係数を割り切らないことと同値
      guard $ P.isSquareFree f_mod_p
      let fs :: [UPolynomial (PrimeField p)]
          fs = [assert (n==1) fi | (fi,n) <- P.factor f_mod_p]
      return $ lift f fs

{-
Suppose @g@ is a factor of @f@.

From Landau-Mignotte inequality,
  @sum [abs c | (c,_) <- mapCoeff ((lc f / lc g) *) $ terms g] <= 2^(deg g) * norm2 f@ holds.

This together with @deg g <= deg f@ implies
  @all [- 2^(deg f) * norm2 f <= c <= 2^(deg f) * norm2 f | (c,_) <- terms ((lc f / lc g) * g)]@.

Choose smallest @k@ such that @p^k / 2 > 2^(deg f) * norm2 f@, so that
  @all [- (p^k)/2 < c < (p^k)/2 | (c,_) <- terms ((lc f / lc g) * g)]@.

Then it call @search@ to look for actual factorization.
-}
lift :: forall p. TL.Nat p => UPolynomial Integer -> [UPolynomial (PrimeField p)] -> [UPolynomial Integer]
lift f [_] = [f]
lift f fs  = search pk f (Hensel.hensel f fs k)
  where
    p = TL.toInt (undefined :: p)
    k, pk :: Integer
    (k,pk) = head [(k,pk) | k <- [1,2..], let pk = p^k, pk^(2::Int) > (2^(P.deg f + 1))^(2::Int) * norm2sq f]

search :: Integer -> UPolynomial Integer -> [UPolynomial Integer] -> [UPolynomial Integer]
search pk f0 fs0 = runST $ do
  let a = P.lc P.grlex f0
      m = length fs0

  fRef   <- newSTRef f0
  fsRef  <- newSTRef fs0
  retRef <- newSTRef []

  forM_ [1 .. m `div` 2] $ \l -> do
    fs <- readSTRef fsRef
    forM_ (comb fs l) $ \s -> do
      {-
          A factor @g@ of @f@ must satisfy @(lc f / lc g) * g ≡ product s (mod p^k)@ for some @s@.
          So we construct a candidate of @(lc f / lc g) * g@ from @product s@.
       -}
      let g0 = product s
          -- @g1@ is a candidate of @(lc f / lc g) * g@
          g1 :: UPolynomial Rational
          g1 = P.mapCoeff conv g0
          conv :: Integer -> Rational
          conv b = b3
            where
              b1  = (a % P.lc P.grlex g0) * fromIntegral b
              -- @b1 ≡ b2 (mod p^k)@ and @0 <= b2 < p^k@
              b2  = b1 - (fromIntegral (floor (b1 / pk') :: Integer) * pk')
              -- @b1 ≡ b2 ≡ b3 (mod p^k)@ and @-(p^k)/2 <= b3 <= (p^k)/2@
              b3  = if pk'/2 < b2 then b2 - pk' else b2
              pk' = fromIntegral pk

      f <- readSTRef fRef
      let f1 = P.mapCoeff fromInteger f

      when (P.deg g1 > 0 && g1 `P.divides` f1) $ do
        let g2 = P.mapCoeff numerator $ P.pp g1
            -- we choose leading coefficient to be positive.
            g :: UPolynomial Integer
            g = if P.lc P.grlex g2 < 0 then - g2 else g2
        writeSTRef fRef $! f `div'` g
        modifySTRef retRef (g :)
        modifySTRef fsRef (\\ s)

  f <- readSTRef fRef
  ret <- readSTRef retRef
  if f==1
    then return ret
    else return $ f : ret

-- |f|^2
norm2sq :: Num a => UPolynomial a -> a
norm2sq f = sum [c^(2::Int) | (c,_) <- P.terms f]

div' :: UPolynomial Integer -> UPolynomial Integer -> UPolynomial Integer
div' f1 f2 = assert (and [denominator c == 1 | (c,_) <- P.terms g3]) g4
  where
    g1, g2 :: UPolynomial Rational
    g1 = P.mapCoeff fromInteger f1
    g2 = P.mapCoeff fromInteger f2
    g3 = g1 `P.div` g2
    g4 = P.mapCoeff numerator g3

comb :: [a] -> Int -> [[a]]
comb _ 0      = [[]]
comb [] _     = []
comb (x:xs) n = [x:ys | ys <- comb xs (n-1)] ++ comb xs n

-- ---------------------------------------------------------------------------

test_zassenhaus :: [UPolynomial Integer]
test_zassenhaus = zassenhaus f
  where
    x = P.var X
    f = x^(4::Int) + 4

test_zassenhausWithP :: Maybe [UPolynomial Integer]
test_zassenhausWithP = zassenhausWithP f 7
  where
    x = P.var X
    f = x^(4::Int) + 4

test_zassenhaus2 :: [UPolynomial Integer]
test_zassenhaus2 = zassenhaus f
  where
    x = P.var X
    f = x^(9::Int) - 15*x^(6::Int) - 87*x^(3::Int) - 125

test_foo :: [(UPolynomial Integer, Integer)]
test_foo = actual
  where
    x :: UPolynomial Integer
    x = P.var X   
    f = - (x^(5::Int) + x^(4::Int) + x^(2::Int) + x + 2)
    actual   = factor f
    expected = [(-1,1), (x^(2::Int)+x+1,1), (x^(3::Int)-x+2,1)]

-- ---------------------------------------------------------------------------
