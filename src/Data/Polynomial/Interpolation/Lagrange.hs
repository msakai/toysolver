-- http://en.wikipedia.org/wiki/Lagrange_polynomial
module Data.Polynomial.Interpolation.Lagrange
  ( interpolate
  ) where

import Data.Polynomial

interpolate :: (Eq k, Fractional k) => [(k,k)] -> UPolynomial k
interpolate zs = sum $ do
  (xj,yj) <- zs
  let lj x = product [constant (1 / (xj - xm)) * (x - constant xm) | (xm,_) <- zs, xj /= xm]
  let x = var X
  return $ constant yj * lj x
