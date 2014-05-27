{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Cooper
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (FlexibleInstances)
--
-- Naive implementation of Cooper's algorithm
--
-- Reference:
-- 
-- * <http://hagi.is.s.u-tokyo.ac.jp/pub/staff/hagiya/kougiroku/ronri/5.txt>
-- 
-- * <http://www.cs.cmu.edu/~emc/spring06/home1_files/Presburger%20Arithmetic.ppt>
-- 
-- See also:
--
-- * <http://hackage.haskell.org/package/presburger>
--
-----------------------------------------------------------------------------
module ToySolver.Cooper
    (
    -- * Language of presburger arithmetics
      ExprZ
    , Lit (..)
    , QFFormula (..)
    , fromLAAtom
    , (.|.)

    -- * Projection
    , project
    , projectCases
    , projectCasesN

    -- * Quantifier elimination
    , eliminateQuantifiers

    -- * Constraint solving
    , solve
    , solveQFFormula
    , solveFormula
    , solveQFLA
    ) where

import ToySolver.Cooper.Core
import ToySolver.Cooper.FOL
