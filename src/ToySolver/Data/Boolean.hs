{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.Boolean
-- Copyright   :  (c) Masahiro Sakai 2012-2015
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Type classes for lattices and boolean algebras.
--
-----------------------------------------------------------------------------
module ToySolver.Data.Boolean
  (
  -- * Boolean algebra
    MonotoneBoolean (..)
  , Complement (..)
  , IfThenElse (..)
  , iteBoolean
  , Boolean (..)
  ) where

import Control.Arrow

infixr 3 .&&.
infixr 2 .||.
infixr 1 .=>.
infix 1 .<=>.

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

  andB [] = true
  andB [a] = a
  andB xs = foldr1 (.&&.) xs

  orB [] = false
  orB [a] = a
  orB xs = foldr1 (.||.) xs

  {-# MINIMAL ((true, (.&&.)) | andB), ((false, (.||.)) | orB) #-}

-- | types that can be negated.
class Complement a where
  notB :: a -> a

class IfThenElse b a where
  ite :: b -> a -> a -> a

iteBoolean :: Boolean a => a -> a -> a -> a
iteBoolean c t e = (c .&&. t) .||. (notB c .&&. e)

-- | types that can be combined with boolean operations.
class (MonotoneBoolean a, Complement a, IfThenElse a a) => Boolean a where
  (.=>.), (.<=>.) :: a -> a -> a

  x .=>. y = notB x .||. y
  x .<=>. y = (x .=>. y) .&&. (y .=>. x)


instance (Complement a, Complement b) => Complement (a, b) where
  notB (a,b) = (notB a, notB b)

instance (MonotoneBoolean a, MonotoneBoolean b) => MonotoneBoolean (a, b) where
  true = (true, true)
  false = (false, false)
  (xs1,ys1) .&&. (xs2,ys2) = (xs1 .&&. xs2, ys1 .&&. ys2)
  (xs1,ys1) .||. (xs2,ys2) = (xs1 .||. xs2, ys1 .||. ys2)
  andB = (andB *** andB) . unzip
  orB  = (orB *** orB) . unzip

instance (Boolean a, Boolean b) => IfThenElse (a, b) (a, b) where
  ite (c1,c2) (t1,t2) (e1,e2) = (ite c1 t1 e1, ite c2 t2 e2)

instance (Boolean a, Boolean b) => Boolean (a, b) where
  (xs1,ys1) .=>. (xs2,ys2) = (xs1 .=>. xs2, ys1 .=>. ys2)
  (xs1,ys1) .<=>. (xs2,ys2) = (xs1 .<=>. xs2, ys1 .<=>. ys2)

instance Complement a => Complement (b -> a) where
  notB f = \x -> notB (f x)

instance MonotoneBoolean a => MonotoneBoolean (b -> a) where
  true = const true
  false = const false
  f .&&. g = \x -> f x .&&. g x
  f .||. g = \x -> f x .||. g x
  andB fs = \x -> andB [f x | f <- fs]
  orB fs = \x -> orB [f x | f <- fs]

instance (Boolean a) => IfThenElse (b -> a) (b -> a) where
  ite c t e = \x -> ite (c x) (t x) (e x)

instance (Boolean a) => Boolean (b -> a) where
  f .=>. g = \x -> f x .=>. g x
  f .<=>. g = \x -> f x .<=>. g x


instance Complement Bool where
  notB = not

instance MonotoneBoolean Bool where
  true  = True
  false = False
  (.&&.) = (&&)
  (.||.) = (||)

instance IfThenElse Bool Bool where
  ite c t e = if c then t else e

instance Boolean Bool where
  (.<=>.) = (==)
