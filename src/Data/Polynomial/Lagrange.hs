-- http://en.wikipedia.org/wiki/Lagrange_polynomial
module Data.Polynomial.Lagrange
  ( interpolation
  ) where

import Data.Polynomial

interpolation :: (Eq k, Fractional k) => [(k,k)] -> UPolynomial k
interpolation zs = sum $ do
  (xj,yj) <- zs
  let lj x = product [constant (1 / (xj - xm)) * (x - constant xm) | (xm,_) <- zs, xj /= xm]
  let x = var ()
  return $ constant yj * lj x
