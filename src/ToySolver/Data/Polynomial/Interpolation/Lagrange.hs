-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.Polynomial.Interpolation.Lagrange
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- References:
--
-- * Lagrange polynomial <http://en.wikipedia.org/wiki/Lagrange_polynomial>
--
-----------------------------------------------------------------------------
module ToySolver.Data.Polynomial.Interpolation.Lagrange
  ( interpolate
  ) where

import ToySolver.Data.Polynomial (UPolynomial, X (..))
import qualified ToySolver.Data.Polynomial as P

interpolate :: (Eq k, Fractional k) => [(k,k)] -> UPolynomial k
interpolate zs = sum $ do
  (xj,yj) <- zs
  let lj x = product [P.constant (1 / (xj - xm)) * (x - P.constant xm) | (xm,_) <- zs, xj /= xm]
  let x = P.var X
  return $ P.constant yj * lj x
