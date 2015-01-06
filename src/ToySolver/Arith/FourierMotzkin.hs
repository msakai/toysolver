{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Arith.FourierMotzkin
-- Copyright   :  (c) Masahiro Sakai 2011-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Naïve implementation of Fourier-Motzkin Variable Elimination
-- 
-- Reference:
--
-- * <http://users.cecs.anu.edu.au/~michaeln/pubs/arithmetic-dps.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.Arith.FourierMotzkin
    (
    -- * Primitive constraints
      Constr (..)
    -- * Projection
    , project
    , projectN
    -- * Quantifier elimination
    , eliminateQuantifiers
    -- * Constraint solving
    , solveFormula
    , solve
    ) where

import ToySolver.Arith.FourierMotzkin.Base
import ToySolver.Arith.FourierMotzkin.FOL
