{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Internal.Data.Vec
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Simple 1-dimentional resizable array
--
-----------------------------------------------------------------------------
module ToySolver.Internal.Data.Vec
  (
  -- * Vec type
    GenericVec
  , Vec
  , UVec
  , IOVec
  , IOUVec
  , Index

  -- * Constructors
  , new
  , clone

  -- * Operators
  , getSize
  , read
  , write
  , modify
  , modify'
  , unsafeRead
  , unsafeWrite
  , unsafeModify
  , unsafeModify'
  , resize
  , growTo
  , push
  , pop
  , popMaybe
  , unsafePop
  , peek
  , unsafePeek
  , clear
  , getElems

  -- * Low-level operators
  , getArray
  , getCapacity
  , resizeCapacity
  ) where

import Prelude hiding (read)

import Control.Loop
import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Data.Ix
import qualified Data.Array.Base as A
import qualified Data.Array.ST as A
import Data.Primitive.MutVar
import Data.Primitive.PrimVar

data GenericVec s a e = GenericVec {-# UNPACK #-} !(PrimVar s Int) {-# UNPACK #-} !(MutVar s (a Index e))
  deriving Eq

type Vec s e = GenericVec s (A.STArray s) e
type UVec s e = GenericVec s (A.STUArray s) e

type IOVec e = Vec RealWorld e
type IOUVec e = UVec RealWorld e

type Index = Int

{- INLINE readArray #-}
readArray :: A.MArray a e m => a Index e -> Index -> m e
#ifdef EXTRA_BOUNDS_CHECKING
readArray = A.readArray
#else
readArray = A.unsafeRead
#endif

{- INLINE writeArray #-}
writeArray :: A.MArray a e m => a Index e -> Index -> e -> m ()
#ifdef EXTRA_BOUNDS_CHECKING
writeArray = A.writeArray
#else
writeArray = A.unsafeWrite
#endif

new :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => m (GenericVec (PrimState m) a e)
new = stToPrim $ do
  sizeRef <- newPrimVar 0
  arrayRef <- newMutVar =<< A.newArray_ (0,-1)
  return $ GenericVec sizeRef arrayRef

{- INLINE getSize #-}
-- | Get the internal representation array
getSize :: PrimMonad m => GenericVec (PrimState m) a e -> m Int
getSize (GenericVec sizeRef _) = stToPrim $ readPrimVar sizeRef

{-# SPECIALIZE read :: PrimMonad m => Vec (PrimState m) e -> Int -> m e #-}
{-# SPECIALIZE read :: PrimMonad m => UVec (PrimState m) Int -> Int -> m Int #-}
{-# SPECIALIZE read :: PrimMonad m => UVec (PrimState m) Double -> Int -> m Double #-}
{-# SPECIALIZE read :: PrimMonad m => UVec (PrimState m) Bool -> Int -> m Bool #-}
read :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> Int -> m e
read !v !i = stToPrim $ do
  a <- getArray v
  s <- getSize v
  if 0 <= i && i < s then
    readArray a i
  else
    error $ "ToySolver.Internal.Data.Vec.read: index " ++ show i ++ " out of bounds"

{-# SPECIALIZE write :: PrimMonad m => Vec (PrimState m) e -> Int -> e -> m () #-}
{-# SPECIALIZE write :: PrimMonad m => UVec (PrimState m) Int -> Int -> Int -> m () #-}
{-# SPECIALIZE write :: PrimMonad m => UVec (PrimState m) Double -> Int -> Double -> m () #-}
{-# SPECIALIZE write :: PrimMonad m => UVec (PrimState m) Bool -> Int -> Bool -> m () #-}
write :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> Int -> e -> m ()
write !v !i e = stToPrim $ do
  a <- getArray v
  s <- getSize v
  if 0 <= i && i < s then
    writeArray a i e
  else
    error $ "ToySolver.Internal.Data.Vec.write: index " ++ show i ++ " out of bounds"

{-# INLINE modify #-}
modify :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> Int -> (e -> e) -> m ()
modify !v !i f = stToPrim $ do
  a <- getArray v
  s <- getSize v
  if 0 <= i && i < s then do
    x <- readArray a i
    writeArray a i (f x)
  else
    error $ "ToySolver.Internal.Data.Vec.modify: index " ++ show i ++ " out of bounds"

{-# INLINE modify' #-}
modify' :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> Int -> (e -> e) -> m ()
modify' !v !i f = stToPrim $ do
  a <- getArray v
  s <- getSize v
  if 0 <= i && i < s then do
    x <- readArray a i
    writeArray a i $! f x
  else
    error $ "ToySolver.Internal.Data.Vec.modify': index " ++ show i ++ " out of bounds"

{-# INLINE unsafeModify #-}
unsafeModify :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> Int -> (e -> e) -> m ()
unsafeModify !v !i f = stToPrim $ do
  a <- getArray v
  x <- readArray a i
  writeArray a i (f x)

{-# INLINE unsafeModify' #-}
unsafeModify' :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> Int -> (e -> e) -> m ()
unsafeModify' !v !i f = stToPrim $ do
  a <- getArray v
  x <- readArray a i
  writeArray a i $! f x

{-# INLINE unsafeRead #-}
unsafeRead :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> Int -> m e
unsafeRead !v !i = stToPrim $ do
  a <- getArray v
  readArray a i

{-# INLINE unsafeWrite #-}
unsafeWrite :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> Int -> e -> m ()
unsafeWrite !v !i e = stToPrim $ do
  a <- getArray v
  writeArray a i e

{-# SPECIALIZE resize :: PrimMonad m => Vec (PrimState m) e -> Int -> m () #-}
{-# SPECIALIZE resize :: PrimMonad m => UVec (PrimState m) Int -> Int -> m () #-}
{-# SPECIALIZE resize :: PrimMonad m => UVec (PrimState m) Double -> Int -> m () #-}
{-# SPECIALIZE resize :: PrimMonad m => UVec (PrimState m) Bool -> Int -> m () #-}
resize :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> Int -> m ()
resize v@(GenericVec sizeRef arrayRef) !n = stToPrim $ do
  a <- getArray v
  capa <- getCapacity v
  unless (n <= capa) $ do
    let capa' = max 2 (capa * 3 `div` 2)
    a' <- A.newArray_ (0, capa'-1)
    copyTo a a' (0,capa-1)
    writeMutVar arrayRef a'
  writePrimVar sizeRef n

{-# SPECIALIZE growTo :: PrimMonad m => Vec (PrimState m) e -> Int -> m () #-}
{-# SPECIALIZE growTo :: PrimMonad m => UVec (PrimState m) Int -> Int -> m () #-}
{-# SPECIALIZE growTo :: PrimMonad m => UVec (PrimState m) Double -> Int -> m () #-}
{-# SPECIALIZE growTo :: PrimMonad m => UVec (PrimState m) Bool -> Int -> m () #-}
growTo :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> Int -> m ()
growTo v !n = stToPrim $ do
  m <- getSize v
  when (m < n) $ resize v n

{-# SPECIALIZE push :: PrimMonad m => Vec (PrimState m) e -> e -> m () #-}
{-# SPECIALIZE push :: PrimMonad m => UVec (PrimState m) Int -> Int -> m () #-}
{-# SPECIALIZE push :: PrimMonad m => UVec (PrimState m) Double -> Double -> m () #-}
{-# SPECIALIZE push :: PrimMonad m => UVec (PrimState m) Bool -> Bool -> m () #-}
push :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> e -> m ()
push v e = stToPrim $ do
  s <- getSize v
  resize v (s+1)
  unsafeWrite v s e

popMaybe :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> m (Maybe e)
popMaybe v = stToPrim $ do
  s <- getSize v
  if s == 0 then
    return Nothing
  else do
    e <- unsafeRead v (s-1)
    resize v (s-1)
    return (Just e)

{-# SPECIALIZE unsafePop :: PrimMonad m => Vec (PrimState m) e -> m e #-}
{-# SPECIALIZE unsafePop :: PrimMonad m => UVec (PrimState m) Int -> m Int #-}
{-# SPECIALIZE unsafePop :: PrimMonad m => UVec (PrimState m) Double -> m Double #-}
{-# SPECIALIZE unsafePop :: PrimMonad m => UVec (PrimState m) Bool -> m Bool #-}
pop :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> m e
pop v = stToPrim $ do
  s <- getSize v
  if s == 0 then
    error $ "ToySolver.Internal.Data.Vec.pop: empty Vec"
  else do
    e <- unsafeRead v (s-1)
    resize v (s-1)
    return e

{-# SPECIALIZE unsafePop :: PrimMonad m => Vec (PrimState m) e -> m e #-}
{-# SPECIALIZE unsafePop :: PrimMonad m => UVec (PrimState m) Int -> m Int #-}
{-# SPECIALIZE unsafePop :: PrimMonad m => UVec (PrimState m) Double -> m Double #-}
{-# SPECIALIZE unsafePop :: PrimMonad m => UVec (PrimState m) Bool -> m Bool #-}
unsafePop :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> m e
unsafePop v = stToPrim $ do
  s <- getSize v
  e <- unsafeRead v (s-1)
  resize v (s-1)
  return e

{-# INLINE peek #-}
peek :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> m e
peek v = stToPrim $ do
  s <- getSize v
  if s == 0 then
    error $ "ToySolver.Internal.Data.Vec.peek: empty Vec"
  else do
    unsafeRead v (s-1)

{-# INLINE unsafePeek #-}
unsafePeek :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> m e
unsafePeek v = stToPrim $ do
  s <- getSize v
  unsafeRead v (s-1)

clear :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> m ()
clear v = resize v 0

getElems :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> m [e]
getElems v = stToPrim $ do
  s <- getSize v
  forM [0..s-1] $ \i -> unsafeRead v i

{-# SPECIALIZE clone :: PrimMonad m => Vec (PrimState m) e -> m (Vec (PrimState m) e) #-}
{-# SPECIALIZE clone :: PrimMonad m => UVec (PrimState m) Int -> m (UVec (PrimState m) Int) #-}
{-# SPECIALIZE clone :: PrimMonad m => UVec (PrimState m) Double -> m (UVec (PrimState m) Double) #-}
{-# SPECIALIZE clone :: PrimMonad m => UVec (PrimState m) Bool -> m (UVec (PrimState m) Bool) #-}
clone :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> m (GenericVec (PrimState m) a e)
clone (GenericVec sizeRef arrayRef) = stToPrim $ do
  a <- readMutVar arrayRef
  arrayRef' <- newMutVar =<< cloneArray a
  sizeRef'  <- newPrimVar =<< readPrimVar sizeRef
  return $ GenericVec sizeRef' arrayRef'

{--------------------------------------------------------------------

--------------------------------------------------------------------}

{-# INLINE getArray #-}
-- | Get the internal representation array
getArray :: PrimMonad m => GenericVec (PrimState m) a e -> m (a Index e)
getArray (GenericVec _ arrayRef) = stToPrim $ readMutVar arrayRef

{-# INLINE getCapacity #-}
-- | Get the internal representation array
getCapacity :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> m Int
getCapacity vec = stToPrim $ liftM rangeSize $ A.getBounds =<< getArray vec

{-# SPECIALIZE resizeCapacity :: PrimMonad m => Vec (PrimState m) e -> Int -> m () #-}
{-# SPECIALIZE resizeCapacity :: PrimMonad m => UVec (PrimState m) Int -> Int -> m () #-}
{-# SPECIALIZE resizeCapacity :: PrimMonad m => UVec (PrimState m) Double -> Int -> m () #-}
{-# SPECIALIZE resizeCapacity :: PrimMonad m => UVec (PrimState m) Bool -> Int -> m () #-}
-- | Pre-allocate internal buffer for @n@ elements.
resizeCapacity :: (PrimMonad m, A.MArray a e (ST (PrimState m))) => GenericVec (PrimState m) a e -> Int -> m ()
resizeCapacity (GenericVec sizeRef arrayRef) capa = stToPrim $ do
  n <- readPrimVar sizeRef
  arr <- readMutVar arrayRef
  capa0 <- liftM rangeSize $ A.getBounds arr
  when (capa0 < capa) $ do
    let capa' = max capa (n * 3 `div` 2)
    arr' <- A.newArray_ (0, capa'-1)
    copyTo arr arr' (0, n-1)
    writeMutVar arrayRef arr'

{--------------------------------------------------------------------
  utility
--------------------------------------------------------------------}

{-# INLINE cloneArray #-}
cloneArray :: (A.MArray a e m) => a Index e -> m (a Index e)
cloneArray arr = do
  b <- A.getBounds arr
  arr' <- A.newArray_ b
  copyTo arr arr' b
  return arr'

{-# INLINE copyTo #-}
copyTo :: (A.MArray a e m) => a Index e -> a Index e -> (Index,Index) -> m ()
copyTo fromArr toArr (!lb,!ub) = do
  forLoop lb (<=ub) (+1) $ \i -> do
    val_i <- readArray fromArr i
    writeArray toArr i val_i
