module Data.Polynomial.Factorization.Rational
  ( factor
  ) where

import Data.List (foldl')
import Data.Polynomial (UPolynomial)
import qualified Data.Polynomial as P
import qualified Data.Polynomial.Factorization.Integer as FactorZ
import Data.Ratio

factor :: UPolynomial Rational -> [(UPolynomial Rational, Integer)]
factor 0 = [(0,1)]
factor p = [(P.constant c, 1) | c /= 1] ++ qs2
  where
    qs  = FactorZ.factor $ P.mapCoeff numerator $ P.pp p
    qs2 = [(P.mapCoeff fromInteger q, m) | (q,m) <- qs, P.deg q > 0]
    c   = toRational (product [(P.coeff P.mone q)^m | (q,m) <- qs, P.deg q == 0]) * P.cont p
