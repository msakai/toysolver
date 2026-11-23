{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Internal.Data.PriorityQueue
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
  , rebuild
  , getHeapArray
  , getHeapVec

  -- * Misc operations
  , resizeHeapCapacity
  ) where

import Control.Loop
import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import qualified Data.Array.ST as A
import Data.Queue.Classes
import qualified ToySolver.Internal.Data.Vec as Vec

type Index = Int

-- | Priority queue implemented as array-based binary heap.
data PriorityQueue s a
  = PriorityQueue
  { lt   :: !(a -> a -> ST s Bool)
  , heap :: !(Vec.Vec s a)
  }

-- | Build a priority queue with default ordering ('(<)' of 'Ord' class)
newPriorityQueue :: forall m a. (PrimMonad m, Ord a) => m (PriorityQueue (PrimState m) a)
newPriorityQueue = newPriorityQueueBy (\a b -> return (a < b) :: ST (PrimState m) Bool)

-- | Build a priority queue with a given /less than/ operator.
newPriorityQueueBy :: (PrimMonad m, PrimBase m1, PrimState m ~ PrimState m1) => (a -> a -> m1 Bool) -> m (PriorityQueue (PrimState m) a)
newPriorityQueueBy cmp = stToPrim $ do
  vec <- Vec.new
  return $ PriorityQueue{ lt = \a b -> primToST (cmp a b), heap = vec }

-- | Return a list of all the elements of a priority queue. (not sorted)
getElems :: PrimMonad m => PriorityQueue (PrimState m) a -> m [a]
getElems q = Vec.getElems (heap q)

-- | Remove all elements from a priority queue.
clear :: PrimMonad m => PriorityQueue (PrimState m) a -> m ()
clear q = Vec.clear (heap q)

-- | Create a copy of a priority queue.
clone :: PrimMonad m => PriorityQueue (PrimState m) a -> m (PriorityQueue (PrimState m) a)
clone q = stToPrim $ do
  h2 <- Vec.clone (heap q)
  return $ PriorityQueue{ lt = lt q, heap = h2 }

instance (PrimMonad m, Ord a, s ~ PrimState m) => NewFifo (PriorityQueue s a) m where
  newFifo = newPriorityQueue

instance (PrimMonad m, s ~ PrimState m) => Enqueue (PriorityQueue s a) m a where
  enqueue q val = stToPrim $ do
    n <- Vec.getSize (heap q)
    Vec.push (heap q) val
    up q n

instance (PrimMonad m, s ~ PrimState m) => Dequeue (PriorityQueue s a) m a where
  dequeue q = stToPrim $ do
    n <- Vec.getSize (heap q)
    case n of
      0 ->
        return Nothing
      _ -> do
        val <- Vec.unsafeRead (heap q) 0
        if n == 1 then do
          Vec.resize (heap q) (n-1)
        else do
          val1 <- Vec.unsafePop (heap q)
          Vec.unsafeWrite (heap q) 0 val1
          down q 0
        return (Just val)

  dequeueBatch q = stToPrim $ go []
    where
      go :: [a] -> ST (PrimState m) [a]
      go xs = do
        r <- dequeue q
        case r of
          Nothing -> return (reverse xs)
          Just x -> go (x:xs)

instance (PrimMonad m, s ~ PrimState m) => QueueSize (PriorityQueue s a) m where
  queueSize q = Vec.getSize (heap q)

up :: PriorityQueue s a -> Index -> ST s ()
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

down :: PriorityQueue s a -> Index -> ST s ()
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

rebuild :: PrimMonad m => PriorityQueue (PrimState m) a -> m ()
rebuild q = stToPrim $ do
  n <- Vec.getSize (heap q)
  forLoop 0 (<n) (+1) $ \i -> do
    up q i

-- | Get the internal representation of a given priority queue.
getHeapArray :: PrimMonad m => PriorityQueue (PrimState m) a -> m (A.STArray (PrimState m) Index a)
getHeapArray q = Vec.getArray (heap q)

-- | Get the internal representation of a given priority queue.
getHeapVec :: PrimMonad m => PriorityQueue (PrimState m) a -> m (Vec.Vec (PrimState m) a)
getHeapVec q = return (heap q)

-- | Pre-allocate internal buffer for @n@ elements.
resizeHeapCapacity :: PrimMonad m => PriorityQueue (PrimState m) a -> Int -> m ()
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

_checkHeapProperty :: PrimMonad m => String -> PriorityQueue (PrimState m) a -> m ()
_checkHeapProperty str q = stToPrim $ do
  n <- Vec.getSize (heap q)
  let go i = do
        val <- Vec.read (heap q) i
        forM_ [left i, right i] $ \j ->
          when (j < n) $ do
            val2 <- Vec.read (heap q) j
            b <- lt q val2 val
            when b $ do
              error (str ++ ": invalid heap " ++ show j)
            go j
  when (n > 0) $ go 0
