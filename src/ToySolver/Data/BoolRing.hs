{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.BoolRing
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Data.BoolRing
  ( BoolRing (..)
  ) where

import Data.Ix
import Data.Typeable
import Data.Generics

newtype BoolRing = BoolRing Bool
  deriving (Eq, Show, Read, Enum, Ord, Ix, Data, Typeable)

instance Num BoolRing where
  BoolRing a + BoolRing b = BoolRing (a /= b) -- xor
  BoolRing a * BoolRing b = BoolRing (a && b)
  negate (BoolRing x) = BoolRing (not x)
  abs x = x
  signum _ = BoolRing True
  fromInteger i = BoolRing (i `mod` 2 == 1)
