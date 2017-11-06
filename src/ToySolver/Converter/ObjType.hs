{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.ObjType
-- Copyright   :  (c) Masahiro Sakai 2011-2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.ObjType
  ( ObjType (..)
  ) where

data ObjType = ObjNone | ObjMaxOne | ObjMaxZero
  deriving (Eq, Ord, Enum, Bounded, Show)
