-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.Polynomial.Factorization.Hensel
-- Copyright   :  (c) Masahiro Sakai 2013-2014
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- References:
--
-- * <http://www.math.kobe-u.ac.jp/Asir/ca.pdf>
--
-- * <http://www14.in.tum.de/konferenzen/Jass07/courses/1/Bulwahn/Buhlwahn_Paper.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.Data.Polynomial.Factorization.Hensel
  ( hensel
  ) where

import ToySolver.Data.Polynomial.Factorization.Hensel.Internal (hensel)
