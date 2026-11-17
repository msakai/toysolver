{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
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
import Control.Monad.Primitive
import Control.Monad.ST
import qualified Data.Array.ST as A
import Data.Queue.Classes
import qualified ToySolver.Internal.Data.Vec as Vec
#ifdef UNBOXED_COMPARISON_ARGUMENTS
import GHC.Exts
#endif

type Index = Int
type Value = Int

-- | Priority queue implemented as array-based binary heap.
data PriorityQueue s
  = PriorityQueue
#ifdef UNBOXED_COMPARISON_ARGUMENTS
  { lt#  :: !(Int# -> Int# -> ST s Bool)
#else
  { lt   :: !(Value -> Value -> ST s Bool)
#endif
  , heap :: !(Vec.UVec s Value)
  , table  :: !(Vec.UVec s Index)
  }

-- | Build a priority queue with default ordering ('(<)' of 'Ord' class)
newPriorityQueue :: forall m. PrimMonad m => m (PriorityQueue (PrimState m))
newPriorityQueue = newPriorityQueueBy (\a b -> return (a < b) :: ST (PrimState m) Bool)

#ifdef UNBOXED_COMPARISON_ARGUMENTS

{-# INLINE newPriorityQueueBy #-}
-- | Build a priority queue with a given /less than/ operator.
newPriorityQueueBy :: (PrimMonad m, PrimBase m1, PrimState m ~ PrimState m1) => (Value -> Value -> m1 Bool) -> m (PriorityQueue (PrimState m))
newPriorityQueueBy cmp = newPriorityQueueBy# cmp#
  where
    cmp# a b = cmp (I# a) (I# b)

-- | Build a priority queue with a given /less than/ operator.
newPriorityQueueBy# :: (PrimMonad m, PrimBase m1, PrimState m ~ PrimState m1) => (Int# -> Int# -> m1 Bool) -> m (PriorityQueue (PrimState m))
newPriorityQueueBy# cmp# = stToPrim $ do
  vec <- Vec.new
  idx <- Vec.new
  return $ PriorityQueue{ lt# = \a b -> primToST (cmp# a b), heap = vec, table = idx }

{-# INLINE lt #-}
lt :: PriorityQueue s -> Value -> Value -> ST s Bool
lt q (I# a) (I# b) = lt# q a b

#else

-- | Build a priority queue with a given /less than/ operator.
newPriorityQueueBy :: (PrimMonad m, PrimBase m1, PrimState m ~ PrimState m1) => (Value -> Value -> m1 Bool) -> m (PriorityQueue (PrimState m))
newPriorityQueueBy cmp = stToPrim $ do
  vec <- Vec.new
  idx <- Vec.new
  return $ PriorityQueue{ lt = cmp, heap = vec, table = idx }

#endif

-- | Return a list of all the elements of a priority queue. (not sorted)
getElems :: PrimMonad m => PriorityQueue (PrimState m) -> m [Value]
getElems q = Vec.getElems (heap q)

-- | Remove all elements from a priority queue.
clear :: PrimMonad m => PriorityQueue (PrimState m) -> m ()
clear q = stToPrim $ do
  Vec.clear (heap q)
  Vec.clear (table q)

-- | Create a copy of a priority queue.
clone :: PrimMonad m => PriorityQueue (PrimState m) -> m (PriorityQueue (PrimState m))
clone q = stToPrim $ do
  h2 <- Vec.clone (heap q)
  t2 <- Vec.clone (table q)
  return $ q{ heap = h2, table = t2 }

instance (PrimMonad m, s ~ PrimState m) => NewFifo (PriorityQueue s) m where
  newFifo = newPriorityQueue

instance (PrimMonad m, s ~ PrimState m) => Enqueue (PriorityQueue s) m Value where
  enqueue q val = stToPrim $ do
    m <- member q val
    unless m $ do
      n <- Vec.getSize (heap q)
      Vec.push (heap q) val
      Vec.growTo (table q) (val+1)
      Vec.unsafeWrite (table q) val n
      up q n

instance (PrimMonad m, s ~ PrimState m) => Dequeue (PriorityQueue s) m Value where
  dequeue q = stToPrim $ do
    n <- Vec.getSize (heap q)
    case n of
      0 ->
        return Nothing
      _ -> do
        val <- Vec.unsafeRead (heap q) 0
        Vec.unsafeWrite (table q) val (-1)
        if n == 1 then do
          Vec.resize (heap q) (n-1)
        else do
          val1 <- Vec.unsafePop (heap q)
          Vec.unsafeWrite (heap q) 0 val1
          Vec.unsafeWrite (table q) val1 0
          down q 0
        return (Just val)

  dequeueBatch q = stToPrim $ go []
    where
      go :: [Value] -> ST (PrimState m) [Value]
      go xs = do
        r <- dequeue q
        case r of
          Nothing -> return (reverse xs)
          Just x -> go (x:xs)

instance (PrimMonad m, s ~ PrimState m) => QueueSize (PriorityQueue s) m where
  queueSize q = Vec.getSize (heap q)

member :: PrimMonad m => PriorityQueue (PrimState m) -> Value -> m Bool
member q v = stToPrim $ do
  n <- Vec.getSize (table q)
  if n <= v then
    return False
  else do
    i <- Vec.unsafeRead (table q) v
    return $! i /= -1

update :: PrimMonad m => PriorityQueue (PrimState m) -> Value -> m ()
update q v = stToPrim $ do
  i <- Vec.unsafeRead (table q) v
  unless (i == -1) $ do
    up q i
    down q i

up :: PriorityQueue s -> Index -> ST s ()
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
            Vec.unsafeWrite (table q) val_p j
            loop p
          else return j
  j <- loop i
  Vec.unsafeWrite (heap q) j val
  Vec.unsafeWrite (table q) val j

down :: PriorityQueue s -> Index -> ST s ()
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
               Vec.unsafeWrite (table q) val_child j
               loop child
  j <- loop i
  Vec.unsafeWrite (heap q) j val
  Vec.unsafeWrite (table q) val j

rebuild :: PrimMonad m => PriorityQueue (PrimState m) -> m ()
rebuild q = stToPrim $ do
  n <- Vec.getSize (heap q)
  forLoop 0 (<n) (+1) $ \i -> do
    up q i

-- | Get the internal representation of a given priority queue.
getHeapArray :: PrimMonad m => PriorityQueue (PrimState m) -> m (A.STUArray (PrimState m) Index Value)
getHeapArray q = Vec.getArray (heap q)

-- | Get the internal representation of a given priority queue.
getHeapVec :: PrimMonad m => PriorityQueue (PrimState m) -> m (Vec.UVec (PrimState m) Value)
getHeapVec q = return (heap q)

-- | Pre-allocate internal buffer for @n@ elements.
resizeHeapCapacity :: PrimMonad m => PriorityQueue (PrimState m) -> Int -> m ()
resizeHeapCapacity q capa = Vec.resizeCapacity (heap q) capa

-- | Pre-allocate internal buffer for @[0..n-1]@ values.
resizeTableCapacity :: PrimMonad m => PriorityQueue (PrimState m) -> Int -> m ()
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

_checkHeapProperty :: PrimMonad m => String -> PriorityQueue (PrimState m) -> m ()
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

  forM_ [0..n-1] $ \i -> do
    v <- Vec.read (heap q) i
    i' <- Vec.read (table q) v
    when (i /= i') $ error $ str ++ ": invalid index " ++ show (i,v,i')
