{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Algebra.Lattice.Boolean
-- Copyright   :  (c) Masahiro Sakai 2012-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Type classes for lattices and boolean algebras.
-- 
-----------------------------------------------------------------------------
module ToySolver.Algebra.Lattice.Boolean
  (
  -- * Boolean algebra
    Complement (..)
  , Boolean (..)
  , true
  , false
  , (.&&.)
  , (.||.)
  , andB
  , orB
  ) where

import Algebra.Lattice

infixr 3 .&&.
infixr 2 .||.
infix 1 .=>., .<=>.

-- | types that can be negated.
class Complement a where
  notB :: a -> a

-- | types that can be combined with boolean operations.
class (BoundedLattice a, Complement a) => Boolean a where
  (.=>.), (.<=>.) :: a -> a -> a
  x .=>. y = notB x .||. y
  x .<=>. y = (x .=>. y) .&&. (y .=>. x)

-- | alias of 'top'
true :: Boolean a => a
true = top

-- | alias of 'bottom'
false :: Boolean a => a
false = bottom

-- | alias of 'meet'
(.&&.) :: Boolean a => a -> a -> a
(.&&.) = meet

-- | alias of 'join'
(.||.) :: Boolean a => a -> a -> a
(.||.) = join

-- | alias of 'meets'
andB :: Boolean a => [a] -> a
andB = meets

-- | alias of 'joins'
orB :: Boolean a => [a] -> a
orB = joins
