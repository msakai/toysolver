-- http://en.wikipedia.org/wiki/Lagrange_polynomial
module Data.Polynomial.Interpolation.Lagrange
  ( interpolate
  ) where

import Data.Polynomial (UPolynomial, X (..))
import qualified Data.Polynomial as P

interpolate :: (Eq k, Fractional k) => [(k,k)] -> UPolynomial k
interpolate zs = sum $ do
  (xj,yj) <- zs
  let lj x = product [P.constant (1 / (xj - xm)) * (x - P.constant xm) | (xm,_) <- zs, xj /= xm]
  let x = P.var X
  return $ P.constant yj * lj x
