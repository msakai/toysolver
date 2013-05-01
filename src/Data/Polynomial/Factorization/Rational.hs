module Data.Polynomial.Factorization.Rational
  ( factor
  ) where

import Data.List (foldl')
import Data.Polynomial
import qualified Data.Polynomial.Factorization.Integer as FactorZ
import Data.Ratio

factor :: UPolynomial Rational -> [(UPolynomial Rational, Integer)]
factor 0 = [(0,1)]
factor p = [(constant c, 1) | c /= 1] ++ qs2
  where
    s   = foldl' lcm  1 [denominator c | (c,_) <- terms p]
    p'  = mapCoeff (\c -> numerator (c * fromInteger s)) p
    qs  = FactorZ.factor p'
    qs2 = [(mapCoeff fromInteger q, m) | (q,m) <- qs, deg q > 0]
    c   = toRational (product [(coeff mmOne q)^m | (q,m) <- qs, deg q == 0]) / toRational s
