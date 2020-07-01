{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.Polynomial.Factorization.Rational
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Data.Polynomial.Factorization.Rational () where

import Data.List (foldl')
import Data.Ratio

import ToySolver.Data.Polynomial.Base (UPolynomial)
import qualified ToySolver.Data.Polynomial.Base as P
import ToySolver.Data.Polynomial.Factorization.Integer ()

instance P.Factor (UPolynomial Rational) where
  factor 0 = [(0,1)]
  factor p = [(P.constant c, 1) | c /= 1] ++ qs2
    where
      qs  = P.factor $ P.pp p
      qs2 = [(P.mapCoeff fromInteger q, m) | (q,m) <- qs, P.deg q > 0]
      c   = toRational (product [(P.coeff P.mone q)^m | (q,m) <- qs, P.deg q == 0]) * P.cont p
