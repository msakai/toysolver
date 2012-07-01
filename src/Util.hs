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

import Data.Ratio

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

showRational :: Bool -> Rational -> String
showRational asRatio v
  | denominator v == 1 = show (numerator v)
  | asRatio            = show (numerator v) ++ "/" ++ show (denominator v)
  | otherwise          = show (fromRational v :: Double)


{-# INLINE revSequence #-}
revSequence :: Monad m => [m a] -> m [a]
revSequence = go []
  where
    go xs [] = return xs
    go xs (m:ms) = do
      x <- m
      go (x:xs) ms

{-# INLINE revMapM #-}
revMapM :: Monad m => (a -> m b) -> ([a] -> m [b])
revMapM f = revSequence . map f

{-# INLINE revForM #-}
revForM :: Monad m => [a] -> (a -> m b) -> m [b]
revForM = flip revMapM