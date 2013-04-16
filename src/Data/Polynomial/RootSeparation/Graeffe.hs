-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Polynomial.RootSeparation.Graeffe
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
-- 
-- Graeffe's Method
--
-- Reference:
-- 
-- * <http://mathworld.wolfram.com/GraeffesMethod.html>
-- 
-- * <http://en.wikipedia.org/wiki/Graeffe's_method>
-- 
-----------------------------------------------------------------------------

module Data.Polynomial.RootSeparation.Graeffe
  ( NthRoot (..)
  , graeffesMethod
  ) where

import Control.Exception
import qualified Data.IntMap as IM
import Data.Polynomial

data NthRoot = NthRoot !Integer !Rational
  deriving (Show)

graeffesMethod :: UPolynomial Rational -> Int -> [NthRoot]
graeffesMethod p v = xs !! (v - 1)
  where
    xs = map (uncurry g) $ zip [1..] (tail $ iterate f $ toMonic p)

    n = deg p

    g :: Int -> UPolynomial Rational -> [NthRoot]
    g v p = do
      i <- [1::Int .. fromInteger n]
      let yi = if i == 1 then - (b i) else - (b i / b (i-1))
      return $ NthRoot (2 ^ fromIntegral v) yi
      where
        bs = IM.fromList [(fromInteger i, b) | (b,ys) <- terms p, let i = n - mmDegree ys, i /= 0]
        b i = IM.findWithDefault 0 i bs

f :: UPolynomial Rational -> UPolynomial Rational
f p = (-1) ^ (deg p) *
      fromTerms [ (c, mmFromList [assert (e `mod` 2 == 0) (x, e `div` 2) | (x,e) <- mmToList xs])
                | (c,xs) <- terms (p * subst p (\_ -> - var ())) ]

f' :: UPolynomial Rational -> UPolynomial Rational
f' p = fromTerms [(b k, mmFromList [((), n - k)]) | k <- [0..n]]
  where
    n = deg p

    a :: Integer -> Rational
    a k
      | n >= k    = coeff (mmFromList [((), n - k)]) p
      | otherwise = 0

    b :: Integer -> Rational
    b k = (-1)^k * (a k)^2 + 2 * sum [(-1)^j * (a j) * (a (2*k-j)) | j <- [0..k-1]]

test v = graeffesMethod p v
  where
    x = var ()
    p = x^2 - 2

test2 v = graeffesMethod p v
 where
    x = var ()
    p = x^5 - 3*x - 1
