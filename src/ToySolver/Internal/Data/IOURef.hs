{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Internal.Data.IOURef
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Simple unboxed IORef-like type based on IOUArray
--
-----------------------------------------------------------------------------
module ToySolver.Internal.Data.IOURef
  ( IOURef
  , newIOURef
  , readIOURef
  , writeIOURef
  , modifyIOURef
  ) where

import Data.Array.Base
import Data.Array.IO

newtype IOURef a = IOURef (IOUArray Int a) deriving (Eq)

{-# INLINEABLE newIOURef #-}
newIOURef :: (MArray IOUArray a IO) => a -> IO (IOURef a)
newIOURef x = do
  a <- newArray (0,0) x
  return $ IOURef a

{-# INLINEABLE readIOURef #-}
readIOURef :: (MArray IOUArray a IO) => IOURef a -> IO a
readIOURef (IOURef a) = unsafeRead a 0

{-# INLINEABLE writeIOURef #-}
writeIOURef :: (MArray IOUArray a IO) => IOURef a -> a -> IO ()
writeIOURef (IOURef a) x = unsafeWrite a 0 x

{-# INLINEABLE modifyIOURef #-}
modifyIOURef :: (MArray IOUArray a IO) => IOURef a -> (a -> a) -> IO ()
modifyIOURef ref f = do
  x <- readIOURef ref
  writeIOURef ref (f x)
