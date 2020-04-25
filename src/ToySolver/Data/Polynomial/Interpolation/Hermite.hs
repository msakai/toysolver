{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.Polynomial.Interpolation.Hermite
-- Copyright   :  (c) Masahiro Sakai 2020
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- References:
--
-- * Lagrange polynomial <https://en.wikipedia.org/wiki/Hermite_interpolation>
--
-----------------------------------------------------------------------------
module ToySolver.Data.Polynomial.Interpolation.Hermite
  ( interpolate
  ) where

import Data.List (unfoldr)

import ToySolver.Data.Polynomial (UPolynomial, X (..))
import qualified ToySolver.Data.Polynomial as P


-- | Compute a hermite Hermite interpolation from a list
-- \([(x_0, [y_0, y'_0, \ldots y^{(m)}_0]), (x_1, [y_1, y'_1, \ldots y^{(m)}_1]), \ldots]\).
interpolate :: (Eq k, Fractional k) => [(k,[k])] -> UPolynomial k
interpolate xyss = sum $ zipWith (\c p -> P.constant c * p) cs ps
  where
    x = P.var X
    ps = scanl (*) (P.constant 1) [(x - P.constant x') | (x', ys') <- xyss, _ <- ys']
    cs = map head $ dividedDifferenceTable xyss


type D a = Either (a, Int, [a]) ((a, a), a)


dividedDifferenceTable :: forall a. Fractional a => [(a, [a])] -> [[a]]
dividedDifferenceTable xyss = unfoldr f xyss'
  where
    xyss' :: [D a]
    xyss' =
      [ Left (x, len, zipWith (\num den -> num / fromInteger den) ys (scanl (*) 1 [1..]))
      | (x, ys) <- xyss
      , let len = length ys
      ]

    d :: D a -> [a]
    d (Left (_x, n, ys)) = replicate n (head ys)
    d (Right (_, y)) = [y]

    gx1, gx2, gy :: D a -> a
    gx1 (Left (x, _n, _ys)) = x
    gx1 (Right ((x1, _x2), _y)) = x1
    gx2 (Left (x, _n, _ys)) = x
    gx2 (Right ((_x1, x2), _y)) = x2
    gy (Left (_x, _n, ys)) = head ys
    gy (Right (_, y)) = y

    f :: [D a] -> Maybe ([a], [D a])
    f [] = Nothing
    f xs = Just (concatMap d xs, h xs)
      where
        h :: [D a] -> [D a]
        h (z1 : zzs) =
          (case z1 of
             Left (x, n, _ : ys@(_ : _)) -> [Left (x, n-1, ys)]
             _ -> [])
          ++
          (case zzs of
             z2 : _ -> [Right ((gx1 z1, gx2 z2), (gy z2 - gy z1) / (gx2 z2 - gx1 z1))]
             [] -> [])
          ++
          h zzs
        h [] = []
