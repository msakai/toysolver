{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Polynomial.Factorization.Integer
-- Copyright   :  (c) Masahiro Sakai 2012-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (TypeSynonymInstances, FlexibleInstances)
--
-----------------------------------------------------------------------------
module Data.Polynomial.Factorization.Integer () where

-- import Data.Polynomial.Factorization.Kronecker
import qualified Data.Polynomial.Base as P
import Data.Polynomial.Factorization.Zassenhaus

instance P.Factor (P.UPolynomial Integer) where
  factor = factor
