{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Internal.TextUtil
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Internal.TextUtil
  ( readInt
  , readUnsignedInteger
  ) where

#include "MachDeps.h"

import Control.Exception
import Data.Word

{-# INLINABLE readInt #-}
readInt :: String -> Int
readInt ('-':str) = - readUnsignedInt str
readInt str = readUnsignedInt str

{-# INLINABLE readUnsignedInt #-}
readUnsignedInt :: String -> Int
readUnsignedInt str = go 0 str
  where
    go !r [] = r
    go !r (c:cs) = go (r*10 + charToInt c) cs

    charToInt :: Char -> Int
    charToInt '0' = 0
    charToInt '1' = 1
    charToInt '2' = 2
    charToInt '3' = 3
    charToInt '4' = 4
    charToInt '5' = 5
    charToInt '6' = 6
    charToInt '7' = 7
    charToInt '8' = 8
    charToInt '9' = 9

-- | 'read' allocate too many intermediate 'Integer'.
-- Therefore we use this optimized implementation instead.
-- Many intermediate values in this implementation will be optimized
-- away by worker-wrapper transformation and unboxing.
{-# INLINABLE readUnsignedInteger #-}
readUnsignedInteger :: String -> Integer
readUnsignedInteger str = assert (result == read str) $ result
  where
    result :: Integer
    result = go 0 str

    lim :: Word
    lim = maxBound `div` 10

    go :: Integer -> [Char] -> Integer
    go !r [] = r
    go !r ds =
      case go2 0 1 ds of
        (r2,b,ds2) -> go (r * fromIntegral b + fromIntegral r2) ds2

    go2 :: Word -> Word -> [Char] -> (Word, Word, [Char])
    go2 !r !b dds | assert (b > r) (b > lim) = (r,b,dds)
    go2 !r !b []     = (r, b, [])
    go2 !r !b (d:ds) = go2 (r*10 + charToWord d) (b*10) ds

    charToWord :: Char -> Word
    charToWord '0' = 0
    charToWord '1' = 1
    charToWord '2' = 2
    charToWord '3' = 3
    charToWord '4' = 4
    charToWord '5' = 5
    charToWord '6' = 6
    charToWord '7' = 7
    charToWord '8' = 8
    charToWord '9' = 9
