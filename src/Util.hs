{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Util
-- Copyright   :  (c) Masahiro Sakai 2011-2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Some utility functions.
-- 
-----------------------------------------------------------------------------

module Util where

-- | Combining two @Maybe@ values using given function.
combineMaybe :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
combineMaybe _ Nothing y = y
combineMaybe _ x Nothing = x
combineMaybe f (Just x) (Just y) = Just (f x y)

-- | is the number integral?
--
-- @
--    isInteger x = fromInteger (round x) == x
-- @
isInteger :: RealFrac a => a -> Bool
isInteger x = fromInteger (round x) == x

-- | fractional part
-- 
-- @
--   fracPart x = x - fromInteger (floor x)
-- @
fracPart :: RealFrac a => a -> a
fracPart x = x - fromInteger (floor x)
