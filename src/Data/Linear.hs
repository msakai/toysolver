{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Linear
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (MultiParamTypeClasses, FunctionalDependencies)
--
-- Type class of linear spaces.
-- 
-----------------------------------------------------------------------------

module Data.Linear
  ( Module (..)
  , Linear (..)
  ) where

import Data.Ratio

infixl 6 .+., .-.
infixl 7 .*., ./.

-- | The class of R-modules.
class Num r => Module r a | a -> r where
  (.*.) :: r -> a -> a
  -- ^ scalar multiplication

  (.+.) :: a -> a -> a
  -- ^ addition

  lzero :: a
  -- ^ identity of '(.+.)'

  -- | negation
  lnegate :: a -> a
  lnegate x = (-1) .*. x

  -- | subtraction
  (.-.) :: a -> a -> a
  a .-. b = a .+. lnegate b

  lsum :: [a] -> a
  lsum = foldr (.+.) lzero

-- | The class of linear spaces.
class (Module k a, Fractional k) => Linear k a | a -> k where
  -- | division
  (./.) :: a -> k -> a
  a ./. b = (1/b) .*. a

instance Integral a => Module (Ratio a) (Ratio a) where
  (.*.) = (*)
  (.+.) = (+)
  lzero = 0

instance Integral a => Linear (Ratio a) (Ratio a)

instance Module Integer Integer where
  (.*.) = (*)
  (.+.) = (+)
  lzero = 0

instance Module Double Double where
  (.*.) = (*)
  (.+.) = (+)
  lzero = 0

instance Linear Double Double
