{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.PriorityQueue
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (MultiParamTypeClasses, FlexibleInstances, BangPatterns)
--
-- Priority queue implemented as array-based binary heap.
--
-----------------------------------------------------------------------------
module ToySolver.Data.PriorityQueue
  (
  -- * PriorityQueue type
    PriorityQueue
  , Index

  -- * Constructors
  , newPriorityQueue
  , newPriorityQueueBy
  , NewFifo (..)

  -- * Operators
  , getElems
  , clear
  , clone
  , Enqueue (..)
  , Dequeue (..)
  , QueueSize (..)
  , getHeapArray

  -- * Misc operations
  , resizeHeapCapacity
  ) where

import Control.Loop
import Control.Monad
import Data.Ix
import qualified Data.Array.Base as A
import qualified Data.Array.IO as A
import Data.IORef
import Data.Queue.Classes

type Index = Int

-- | Priority queue implemented as array-based binary heap.
data PriorityQueue a
  = PriorityQueue
  { lt   :: !(a -> a -> IO Bool)
  , heap :: !(IORef (Int, A.IOArray Int a))
  }

-- | Build a priority queue with default ordering ('(<)' of 'Ord' class)
newPriorityQueue :: Ord a => IO (PriorityQueue a)
newPriorityQueue = newPriorityQueueBy (\a b -> return (a < b))

-- | Build a priority queue with a given /less than/ operator.
newPriorityQueueBy :: (a -> a -> IO Bool) -> IO (PriorityQueue a)
newPriorityQueueBy cmp = do
  h <- A.newArray_ (0,-1)
  ref <- newIORef (0,h)
  return $ PriorityQueue{ lt = cmp, heap = ref }

-- | Return a list of all the elements of a priority queue. (not sorted)
getElems :: PriorityQueue a -> IO [a]
getElems q = do
  (n,arr) <- readIORef (heap q)
  forM [0..n-1] $ \i -> A.unsafeRead arr i

-- | Remove all elements from a priority queue.
clear :: PriorityQueue a -> IO ()
clear q = do
  (_,arr) <- readIORef (heap q)
  writeIORef (heap q) (0,arr)

-- | Create a copy of a priority queue.
clone :: PriorityQueue a -> IO (PriorityQueue a)
clone q = do
  (n,arr) <- readIORef (heap q)
  arr' <- cloneArray arr
  ref <- newIORef (n,arr')
  return $ PriorityQueue{ lt = lt q, heap = ref }

instance Ord a => NewFifo (PriorityQueue a) IO where
  newFifo = newPriorityQueue

instance Enqueue (PriorityQueue a) IO a where
  enqueue q val = do
    (n,arr) <- readIORef (heap q)
    c <- liftM rangeSize $ A.getBounds arr
    if (n+1 < c)
      then do
        A.unsafeWrite arr n val
        writeIORef (heap q) (n+1,arr)
      else do
        let c' = max 2 (c * 3 `div` 2)
        arr' <- A.newArray_ (0, c'-1)
        copyTo arr arr' (0, n-1)
        A.unsafeWrite arr' n val
        writeIORef (heap q) (n+1,arr')
    up q n

instance Dequeue (PriorityQueue a) IO a where
  dequeue q = do
    (n,arr) <- readIORef (heap q)
    case n of
      0 ->
        return Nothing
      _ -> do
        val <- A.unsafeRead arr 0
        writeIORef (heap q) (n-1, arr)
        when (n > 1) $ do
          val1 <- A.unsafeRead arr (n-1)
          A.unsafeWrite arr 0 val1
          down q 0
        return (Just val)

  dequeueBatch q = go []
    where
      go xs = do
        r <- dequeue q
        case r of
          Nothing -> return (reverse xs)
          Just x -> go (x:xs)

instance QueueSize (PriorityQueue a) IO where
  queueSize q = do
    (n,_) <- readIORef (heap q)
    return n

up :: PriorityQueue a -> Index -> IO ()
up q !i = do
  (_,arr) <- readIORef (heap q)
  val <- A.unsafeRead arr i
  let loop 0 = return 0
      loop j = do
        let p = parent j
        val_p <- A.unsafeRead arr p
        b <- lt q val val_p
        if b
          then do
            A.unsafeWrite arr j val_p
            loop p
          else return j
  j <- loop i
  A.unsafeWrite arr j val

down :: PriorityQueue a -> Index -> IO ()
down q !i = do
  (!n,arr) <- readIORef (heap q)
  val <- A.unsafeRead arr i
  let loop !j = do
        let !l = left j
            !r = right j
        if l >= n
         then return j
         else do
           child <- do
             if r >= n
              then return l
              else do
                val_l <- A.unsafeRead arr l
                val_r <- A.unsafeRead arr r
                b <- lt q val_r val_l
                if b
                  then return r
                  else return l
           val_child <- A.unsafeRead arr child
           b <- lt q val_child val
           if not b
             then return j
             else do
               A.unsafeWrite arr j val_child
               loop child
  j <- loop i
  A.unsafeWrite arr j val

-- | Get the internal representation of a given priority queue.
getHeapArray :: PriorityQueue a -> IO (A.IOArray Index a)
getHeapArray q = liftM snd $ readIORef (heap q)

-- | Pre-allocate internal buffer for @n@ elements.
resizeHeapCapacity :: PriorityQueue a -> Int -> IO ()
resizeHeapCapacity q capa = do
  (n,arr) <- readIORef (heap q)
  capa0 <- liftM rangeSize $ A.getBounds arr
  when (capa0 < capa) $ do
    arr' <- A.newArray_ (0, capa-1)
    copyTo arr arr' (0, n-1)
    writeIORef (heap q) (n,arr')

{--------------------------------------------------------------------
  Index "traversal" functions
--------------------------------------------------------------------}

{-# INLINE left #-}
left :: Index -> Index
left i = i*2 + 1

{-# INLINE right #-}
right :: Index -> Index
right i = (i+1)*2;

{-# INLINE parent #-}
parent :: Index -> Index
parent i = (i-1) `div` 2

{--------------------------------------------------------------------
  utility
--------------------------------------------------------------------}

cloneArray :: (A.MArray a e m) => a Index e -> m (a Index e)
cloneArray arr = do
  b <- A.getBounds arr
  arr' <- A.newArray_ b
  copyTo arr arr' b
  return arr'

copyTo :: (A.MArray a e m) => a Index e -> a Index e -> (Index,Index) -> m ()
copyTo fromArr toArr (!lb,!ub) = do
  forLoop lb (<=ub) (+1) $ \i -> do
    val_i <- A.unsafeRead fromArr i
    A.unsafeWrite toArr i val_i

{--------------------------------------------------------------------
  test
--------------------------------------------------------------------}

{-
checkHeapProperty :: String -> PriorityQueue a -> IO ()
checkHeapProperty str q = do 
  (n,arr) <- readIORef (heap q)
  let go i = do
        val <- A.readArray arr i
        forM_ [left i, right i] $ \j ->
          when (j < n) $ do
            val2 <- A.readArray arr j
            b <- lt q val2 val
            when b $ do
              error (str ++ ": invalid heap " ++ show j)
            go j
  when (n > 0) $ go 0
-}
