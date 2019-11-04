{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.Polynomial.Factorization.Integer
-- Copyright   :  (c) Masahiro Sakai 2012-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (TypeSynonymInstances, FlexibleInstances)
--
-----------------------------------------------------------------------------
module ToySolver.Data.Polynomial.Factorization.Integer () where

-- import ToySolver.Data.Polynomial.Factorization.Kronecker
import qualified ToySolver.Data.Polynomial.Base as P
import ToySolver.Data.Polynomial.Factorization.Zassenhaus

instance P.Factor (P.UPolynomial Integer) where
  factor = factor
