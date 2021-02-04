{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
#ifdef __GLASGOW_HASKELL__
#define UNBOXED_COMPARISON_ARGUMENTS
#endif
#ifdef UNBOXED_COMPARISON_ARGUMENTS
{-# LANGUAGE MagicHash #-}
#endif
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Internal.Data.IndexedPriorityQueue
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Priority queue implemented as array-based binary heap.
--
-----------------------------------------------------------------------------
module ToySolver.Internal.Data.IndexedPriorityQueue
  (
  -- * PriorityQueue type
    PriorityQueue
  , Value
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
  , member
  , update
  , rebuild
  , getHeapArray
  , getHeapVec

  -- * Misc operations
  , resizeHeapCapacity
  , resizeTableCapacity
  ) where

import Control.Loop
import Control.Monad
import qualified Data.Array.IO as A
import Data.Queue.Classes
import qualified ToySolver.Internal.Data.Vec as Vec
#ifdef UNBOXED_COMPARISON_ARGUMENTS
import GHC.Exts
#endif

type Index = Int
type Value = Int

-- | Priority queue implemented as array-based binary heap.
data PriorityQueue
  = PriorityQueue
#ifdef UNBOXED_COMPARISON_ARGUMENTS
  { lt#  :: !(Int# -> Int# -> IO Bool)
#else
  { lt   :: !(Value -> Value -> IO Bool)
#endif
  , heap :: !(Vec.UVec Value)
  , table  :: !(Vec.UVec Index)
  }

-- | Build a priority queue with default ordering ('(<)' of 'Ord' class)
newPriorityQueue :: IO PriorityQueue
newPriorityQueue = newPriorityQueueBy (\a b -> return (a < b))

#ifdef UNBOXED_COMPARISON_ARGUMENTS

{-# INLINE newPriorityQueueBy #-}
-- | Build a priority queue with a given /less than/ operator.
newPriorityQueueBy :: (Value -> Value -> IO Bool) -> IO PriorityQueue
newPriorityQueueBy cmp = newPriorityQueueBy# cmp#
  where
    cmp# a b = cmp (I# a) (I# b)

-- | Build a priority queue with a given /less than/ operator.
newPriorityQueueBy# :: (Int# -> Int# -> IO Bool) -> IO PriorityQueue
newPriorityQueueBy# cmp# = do
  vec <- Vec.new
  idx <- Vec.new
  return $ PriorityQueue{ lt# = cmp#, heap = vec, table = idx }

{-# INLINE lt #-}
lt :: PriorityQueue -> Value -> Value -> IO Bool
lt q (I# a) (I# b) = lt# q a b

#else

-- | Build a priority queue with a given /less than/ operator.
newPriorityQueueBy :: (Value -> Value -> IO Bool) -> IO PriorityQueue
newPriorityQueueBy cmp = do
  vec <- Vec.new
  idx <- Vec.new
  return $ PriorityQueue{ lt = cmp, heap = vec, table = idx }

#endif

-- | Return a list of all the elements of a priority queue. (not sorted)
getElems :: PriorityQueue -> IO [Value]
getElems q = Vec.getElems (heap q)

-- | Remove all elements from a priority queue.
clear :: PriorityQueue -> IO ()
clear q = do
  Vec.clear (heap q)
  Vec.clear (table q)

-- | Create a copy of a priority queue.
clone :: PriorityQueue -> IO PriorityQueue
clone q = do
  h2 <- Vec.clone (heap q)
  t2 <- Vec.clone (table q)
  return $ q{ heap = h2, table = t2 }

instance NewFifo PriorityQueue IO where
  newFifo = newPriorityQueue

instance Enqueue PriorityQueue IO Value where
  enqueue q val = do
    m <- member q val
    unless m $ do
      n <- Vec.getSize (heap q)
      Vec.push (heap q) val
      Vec.growTo (table q) (val+1)
      Vec.write (table q) val n
      up q n

instance Dequeue PriorityQueue IO Value where
  dequeue q = do
    n <- Vec.getSize (heap q)
    case n of
      0 ->
        return Nothing
      _ -> do
        val <- Vec.read (heap q) 0
        Vec.write (table q) val (-1)
        if n == 1 then do
          Vec.resize (heap q) (n-1)
        else do
          val1 <- Vec.pop (heap q)
          Vec.write (heap q) 0 val1
          Vec.write (table q) val1 0
          down q 0
        return (Just val)

  dequeueBatch q = go []
    where
      go :: [Value] -> IO [Value]
      go xs = do
        r <- dequeue q
        case r of
          Nothing -> return (reverse xs)
          Just x -> go (x:xs)

instance QueueSize PriorityQueue IO where
  queueSize q = Vec.getSize (heap q)

member :: PriorityQueue -> Value -> IO Bool
member q v = do
  n <- Vec.getSize (table q)
  if n <= v then
    return False
  else do
    i <- Vec.read (table q) v
    return $! i /= -1

update :: PriorityQueue -> Value -> IO ()
update q v = do
  i <- Vec.read (table q) v
  unless (i == -1) $ do
    up q i
    down q i

up :: PriorityQueue -> Index -> IO ()
up q !i = do
  val <- Vec.read (heap q) i
  let loop 0 = return 0
      loop j = do
        let p = parent j
        val_p <- Vec.read (heap q) p
        b <- lt q val val_p
        if b
          then do
            Vec.write (heap q) j val_p
            Vec.write (table q) val_p j
            loop p
          else return j
  j <- loop i
  Vec.write (heap q) j val
  Vec.write (table q) val j

down :: PriorityQueue -> Index -> IO ()
down q !i = do
  n <- Vec.getSize (heap q)
  val <- Vec.read (heap q) i
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
                val_l <- Vec.read (heap q) l
                val_r <- Vec.read (heap q) r
                b <- lt q val_r val_l
                if b
                  then return r
                  else return l
           val_child <- Vec.read (heap q) child
           b <- lt q val_child val
           if not b
             then return j
             else do
               Vec.write (heap q) j val_child
               Vec.write (table q) val_child j
               loop child
  j <- loop i
  Vec.write (heap q) j val
  Vec.write (table q) val j

rebuild :: PriorityQueue -> IO ()
rebuild q = do
  n <- Vec.getSize (heap q)
  forLoop 0 (<n) (+1) $ \i -> do
    up q i

-- | Get the internal representation of a given priority queue.
getHeapArray :: PriorityQueue -> IO (A.IOUArray Index Value)
getHeapArray q = Vec.getArray (heap q)

-- | Get the internal representation of a given priority queue.
getHeapVec :: PriorityQueue -> IO (Vec.UVec Value)
getHeapVec q = return (heap q)

-- | Pre-allocate internal buffer for @n@ elements.
resizeHeapCapacity :: PriorityQueue -> Int -> IO ()
resizeHeapCapacity q capa = Vec.resizeCapacity (heap q) capa

-- | Pre-allocate internal buffer for @[0..n-1]@ values.
resizeTableCapacity :: PriorityQueue -> Int -> IO ()
resizeTableCapacity q capa = Vec.resizeCapacity (table q) capa

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
