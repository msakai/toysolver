-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Polynomial.Factorization.Integer
-- Copyright   :  (c) Masahiro Sakai 2012-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Data.Polynomial.Factorization.Integer
  ( factor
  ) where

-- import Data.Polynomial.Factorization.Kronecker
import Data.Polynomial.Factorization.Zassenhaus (factor)
