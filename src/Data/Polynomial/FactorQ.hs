module Data.Polynomial.FactorQ
  ( factor
  ) where

import Data.List (foldl')
import Data.Polynomial
import qualified Data.Polynomial.FactorZ as FactorZ
import Data.Ratio

factor :: UPolynomial Rational -> [UPolynomial Rational]
factor 0 = [0]
factor p = [constant c | c /= 1] ++ qs2
  where
    s = foldl' lcm  1 [denominator c | (c,_) <- terms p]
    p' = mapCoeff (\c -> numerator (c * fromInteger s)) p
    qs  = FactorZ.factor p'
    qs2 = [mapCoeff fromInteger q | q <- qs, deg q > 0]
    c   = toRational (product [coeff mmOne q | q <- qs, deg q == 0]) / toRational s
