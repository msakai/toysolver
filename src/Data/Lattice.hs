{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Lattice
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Type classes for lattices and boolean algebras.
-- 
-----------------------------------------------------------------------------
module Data.Lattice
  (
  -- * Lattice
    Lattice (..)
  
  -- * Boolean algebra
  , Complement (..)
  , Boolean (..)
  , true
  , false
  , (.&&.)
  , (.||.)
  , andB
  , orB
  ) where

infixr 3 .&&.
infixr 2 .||.
infix 1 .=>., .<=>.

-- | Type class for lattice.
class Lattice a where
  -- | top element
  top :: a

  -- | bottom element
  bottom :: a

  -- | join
  join :: a -> a -> a

  -- | meet
  meet :: a -> a -> a

  -- | n-ary join
  joinL :: [a] -> a

  -- | n-ary meet
  meetL :: [a] -> a

  joinL = foldr join bottom
  meetL = foldr meet top

-- | types that can be negated.
class Complement a where
  notB :: a -> a

-- | types that can be combined with boolean operations.
class (Lattice a, Complement a) => Boolean a where
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

-- | alias of 'meetL'
andB :: Boolean a => [a] -> a
andB = meetL

-- | alias of 'joinL'
orB :: Boolean a => [a] -> a
orB = joinL
