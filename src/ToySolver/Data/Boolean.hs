{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.Boolean
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Type classes for lattices and boolean algebras.
-- 
-----------------------------------------------------------------------------
module ToySolver.Data.Boolean
  (
  -- * Boolean algebra
    MonotoneBoolean (..)
  , Complement (..)
  , Boolean (..)
  , andB
  , orB
  ) where

infixr 3 .&&.
infixr 2 .||.
infix 1 .=>., .<=>.

class MonotoneBoolean a where
  true, false :: a
  (.&&.) :: a -> a -> a
  (.||.) :: a -> a -> a

-- | types that can be negated.
class Complement a where
  notB :: a -> a

-- | types that can be combined with boolean operations.
class (MonotoneBoolean a, Complement a) => Boolean a where
  (.=>.), (.<=>.) :: a -> a -> a
  x .=>. y = notB x .||. y
  x .<=>. y = (x .=>. y) .&&. (y .=>. x)

andB :: MonotoneBoolean a => [a] -> a
andB = foldr (.&&.) true

orB :: MonotoneBoolean a => [a] -> a
orB = foldr (.||.) false

instance Complement Bool where
  notB = not

instance MonotoneBoolean Bool where
  true  = True
  false = False
  (.&&.) = (&&)
  (.||.) = (||)

instance Boolean Bool where
  (.<=>.) = (==)
