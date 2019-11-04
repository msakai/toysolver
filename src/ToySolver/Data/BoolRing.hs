{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
