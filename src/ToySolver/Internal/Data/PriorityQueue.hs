{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Internal.Data.PriorityQueue
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
module ToySolver.Internal.Data.PriorityQueue
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
  , getHeapVec

  -- * Misc operations
  , resizeHeapCapacity
  ) where

import Control.Monad
import qualified Data.Array.IO as A
import Data.Queue.Classes
import qualified ToySolver.Data.Vec as Vec

type Index = Int

-- | Priority queue implemented as array-based binary heap.
data PriorityQueue a
  = PriorityQueue
  { lt   :: !(a -> a -> IO Bool)
  , heap :: !(Vec.Vec a)
  }

-- | Build a priority queue with default ordering ('(<)' of 'Ord' class)
newPriorityQueue :: Ord a => IO (PriorityQueue a)
newPriorityQueue = newPriorityQueueBy (\a b -> return (a < b))

-- | Build a priority queue with a given /less than/ operator.
newPriorityQueueBy :: (a -> a -> IO Bool) -> IO (PriorityQueue a)
newPriorityQueueBy cmp = do
  vec <- Vec.new
  return $ PriorityQueue{ lt = cmp, heap = vec }

-- | Return a list of all the elements of a priority queue. (not sorted)
getElems :: PriorityQueue a -> IO [a]
getElems q = Vec.getElems (heap q)

-- | Remove all elements from a priority queue.
clear :: PriorityQueue a -> IO ()
clear q = Vec.clear (heap q)

-- | Create a copy of a priority queue.
clone :: PriorityQueue a -> IO (PriorityQueue a)
clone q = do
  h2 <- Vec.clone (heap q)
  return $ PriorityQueue{ lt = lt q, heap = h2 }

instance Ord a => NewFifo (PriorityQueue a) IO where
  newFifo = newPriorityQueue

instance Enqueue (PriorityQueue a) IO a where
  enqueue q val = do
    n <- Vec.getSize (heap q)
    Vec.push (heap q) val
    up q n

instance Dequeue (PriorityQueue a) IO a where
  dequeue q = do
    n <- Vec.getSize (heap q)
    case n of
      0 ->
        return Nothing
      _ -> do
        val <- Vec.unsafeRead (heap q) 0
        if n == 1 then do
          Vec.resize (heap q) (n-1)
        else do
          val1 <- Vec.unsafeRead (heap q) (n-1)
          Vec.unsafeWrite (heap q) 0 val1
          Vec.resize (heap q) (n-1)
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
  queueSize q = Vec.getSize (heap q)

up :: PriorityQueue a -> Index -> IO ()
up q !i = do
  val <- Vec.unsafeRead (heap q) i
  let loop 0 = return 0
      loop j = do
        let p = parent j
        val_p <- Vec.unsafeRead (heap q) p
        b <- lt q val val_p
        if b
          then do
            Vec.unsafeWrite (heap q) j val_p
            loop p
          else return j
  j <- loop i
  Vec.unsafeWrite (heap q) j val

down :: PriorityQueue a -> Index -> IO ()
down q !i = do
  n <- Vec.getSize (heap q)
  val <- Vec.unsafeRead (heap q) i
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
                val_l <- Vec.unsafeRead (heap q) l
                val_r <- Vec.unsafeRead (heap q) r
                b <- lt q val_r val_l
                if b
                  then return r
                  else return l
           val_child <- Vec.unsafeRead (heap q) child
           b <- lt q val_child val
           if not b
             then return j
             else do
               Vec.unsafeWrite (heap q) j val_child
               loop child
  j <- loop i
  Vec.unsafeWrite (heap q) j val

-- | Get the internal representation of a given priority queue.
getHeapArray :: PriorityQueue a -> IO (A.IOArray Index a)
getHeapArray q = Vec.getArray (heap q)

-- | Get the internal representation of a given priority queue.
getHeapVec :: PriorityQueue a -> IO (Vec.Vec a)
getHeapVec q = return (heap q)

-- | Pre-allocate internal buffer for @n@ elements.
resizeHeapCapacity :: PriorityQueue a -> Int -> IO ()
resizeHeapCapacity q capa = Vec.resizeCapacity (heap q) capa

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
