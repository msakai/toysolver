{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, BangPatterns, DoAndIfThenElse, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  IndexedPriorityQueue
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (MultiParamTypeClasses, FlexibleInstances, BangPatterns, DoAndIfThenElse, TypeSynonymInstances)
--
-- Priority queue implemented as array-based binary heap.
--
-----------------------------------------------------------------------------
module IndexedPriorityQueue
  (
  -- * PriorityQueue type
    PriorityQueue

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
  , member
  , update
  ) where

import Control.Monad
import Data.Ix
import qualified Data.Array.Base as A
import qualified Data.Array.IO as A
import Data.IORef
import Data.Queue.Classes

type Index = Int
type Value = Int

-- | Priority queue implemented as array-based binary heap.
data PriorityQueue
  = PriorityQueue
  { lt 　:: !(Value -> Value -> IO Bool)
  , heap :: !(IORef (Int, A.IOUArray Index Value))
  , table  :: !(IORef (A.IOUArray Value Index))
  }

-- | Build a priority queue with default ordering ('(<)' of 'Ord' class)
newPriorityQueue :: IO PriorityQueue
newPriorityQueue = newPriorityQueueBy (\a b -> return (a < b))

-- | Build a priority queue with a given /less than/ operator.
newPriorityQueueBy :: (Value -> Value -> IO Bool) -> IO (PriorityQueue)
newPriorityQueueBy cmp = do
  h <- A.newArray_ (0,-1)
  ref <- newIORef (0,h)
  idx <- A.newArray_ (0,-1)
  ref2 <- newIORef idx
  return $ PriorityQueue{ lt = cmp, heap = ref, table =ref2 }

-- | Return a list of all the elements of a priority queue. (not sorted)
getElems :: PriorityQueue -> IO [Value]
getElems q = do
  (n,arr) <- readIORef (heap q)
  forM [0..n-1] $ \i -> A.readArray arr i

-- | Remove all elements from a priority queue.
clear :: PriorityQueue -> IO ()
clear q = do
  (_,arr) <- readIORef (heap q)
  writeIORef (heap q) (0,arr)

  idx <- readIORef (table q)
  (!lb,!ub) <- A.getBounds idx
  let go i
        | i > ub    = return ()
        | otherwise = A.unsafeWrite idx i (-1) >> go (i+1)
  go lb

-- | Create a copy of a priority queue.
clone :: PriorityQueue -> IO PriorityQueue
clone q = do
  (n,arr) <- readIORef (heap q)
  arr' <- cloneArray arr
  ref <- newIORef (n,arr')

  idx <- readIORef (table q)
  idx' <- cloneArray idx
  ref2 <- newIORef idx'

  return $ PriorityQueue{ lt = lt q, heap = ref, table = ref2 }

instance Enqueue (PriorityQueue) IO Value where
  enqueue q val = do
    m <- member q val
    unless m $ do
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

      idx <- readIORef (table q)
      c2 <- liftM rangeSize $ A.getBounds idx
      if val < c2
        then A.unsafeWrite idx val n
        else do
          let c2' = max 2 (c2 * 3 `div` 2)
          idx' <- A.newArray_ (0, c2'-1)
          copyTo idx idx' (0, c2-1)
          forM_ [c2..c2'-1] $ \i -> A.unsafeWrite idx' i (-1)
          A.unsafeWrite idx' val n
          writeIORef (table q) idx'
  
      up q n

instance Dequeue (PriorityQueue) IO Value where
  dequeue q = do
    (n,arr) <- readIORef (heap q)
    idx <- readIORef (table q)
    case n of
      0 -> do
        return Nothing
      _ -> do
        val <- A.readArray arr 0
        A.unsafeWrite idx val (-1)
        writeIORef (heap q) (n-1, arr)
        when (n > 1) $ do
          val1 <- A.readArray arr (n-1)
          A.unsafeWrite arr 0 val1
          A.unsafeWrite idx val1 0
          down q 0
        return (Just val)

  dequeueBatch q = go []
    where
      go xs = do
        r <- dequeue q
        case r of
          Nothing -> return (reverse xs)
          Just x -> go (x:xs)

instance QueueSize (PriorityQueue) IO where
  queueSize q = do
    (n,_) <- readIORef (heap q)
    return n

member :: PriorityQueue -> Value -> IO Bool
member q v = do
  idx <- readIORef (table q)
  r <- A.getBounds idx
  if not (inRange r v) then
    return False
  else do
    i <- A.unsafeRead idx v
    return $! i /= -1

update :: PriorityQueue -> Value -> IO ()
update q v = do
  idx <- readIORef (table q)
  i <- A.readArray idx v
  unless (i == -1) $ do
    up q i
    down q i

up :: PriorityQueue -> Index -> IO ()
up q !i = do
  (_,arr) <- readIORef (heap q)
  idx <- readIORef (table q)
  val <- A.readArray arr i
  let loop 0 = return 0
      loop j = do
        let p = parent j
        val_p <- A.readArray arr p
        b <- lt q val val_p
        if b
          then do
            A.unsafeWrite arr j val_p
            A.unsafeWrite idx val_p j
            loop p
          else return j
  j <- loop i
  A.unsafeWrite arr j val
  A.unsafeWrite idx val j

down :: PriorityQueue -> Index -> IO ()
down q !i = do
  (!n,arr) <- readIORef (heap q)
  idx <- readIORef (table q)
  val <- A.readArray arr i
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
                val_l <- A.readArray arr l
                val_r <- A.readArray arr r
                b <- lt q val_r val_l
                if b
                  then return r
                  else return l
           val_child <- A.readArray arr child
           b <- lt q val_child val
           if not b
             then return j
             else do
               A.unsafeWrite arr j val_child
               A.unsafeWrite idx val_child j
               loop child
  j <- loop i
  A.unsafeWrite arr j val
  A.unsafeWrite idx val j

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
copyTo fromArr toArr b = do
  forM_ (range b) $ \i -> do
    val_i <- A.readArray fromArr i
    A.unsafeWrite toArr i val_i

{--------------------------------------------------------------------
  test
--------------------------------------------------------------------}

{-
checkHeapProperty :: String -> PriorityQueue -> IO ()
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

  idx <- readIORef (table q)
  forM_ [0..n-1] $ \i -> do
    v <- A.readArray arr i
    i' <- A.readArray idx v
    when (i /= i') $ error $ str ++ ": invalid index " ++ show (i,v,i')
-}
