module Data.AlgebraicNumber.RealInstance where

import Data.Polynomial as P
import Data.AlgebraicNumber

instance Real AReal where
  toRational x
    | Data.AlgebraicNumber.deg x == 1 =
        let p = minimalPolynomial x
            a = P.coeff (P.mmVar ()) p
            b = P.coeff P.mmOne p
        in - b / a
    | otherwise  = error "toRational: proper algebraic number"

instance RealFrac AReal where
  properFraction = properFraction'
  truncate       = truncate'
  round          = round'
  ceiling        = ceiling'
  floor          = floor'
