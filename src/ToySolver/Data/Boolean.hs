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
  ) where

infixr 3 .&&.
infixr 2 .||.
infix 1 .=>., .<=>.

class MonotoneBoolean a where
  true, false :: a
  (.&&.) :: a -> a -> a
  (.||.) :: a -> a -> a
  andB :: [a] -> a
  orB :: [a] -> a

  true = andB []
  false = orB []
  a .&&. b = andB [a,b]
  a .||. b = orB [a,b]
  andB = foldr (.&&.) true  
  orB = foldr (.||.) false

  {-# MINIMAL ((true, (.&&.)) | andB), ((false, (.||.)) | orB) #-}

-- | types that can be negated.
class Complement a where
  notB :: a -> a

-- | types that can be combined with boolean operations.
class (MonotoneBoolean a, Complement a) => Boolean a where
  (.=>.), (.<=>.) :: a -> a -> a
  x .=>. y = notB x .||. y
  x .<=>. y = (x .=>. y) .&&. (y .=>. x)

instance Complement Bool where
  notB = not

instance MonotoneBoolean Bool where
  true  = True
  false = False
  (.&&.) = (&&)
  (.||.) = (||)

instance Boolean Bool where
  (.<=>.) = (==)
