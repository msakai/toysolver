{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Internal.Data.SeqQueue
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (FlexibleInstances, MultiParamTypeClasses)
--
-- Queue implemented using IORef and Sequence.
-- 
-----------------------------------------------------------------------------
module ToySolver.Internal.Data.SeqQueue
  (
  -- * SeqQueue type
    SeqQueue

  -- * Constructors
  , NewFifo (..)

  -- * Operators  
  , Enqueue (..)
  , Dequeue (..)
  , QueueSize (..)
  , clear
  ) where

import Control.Monad.Primitive
import Control.Monad.ST
import Data.Queue
import Data.Foldable
import Data.Primitive.MutVar
import qualified Data.Sequence as Seq

newtype SeqQueue m a = SeqQueue (MutVar (PrimState m) (Seq.Seq a))

instance PrimMonad m => NewFifo (SeqQueue m a) m where
  {-# SPECIALIZE instance NewFifo (SeqQueue IO a) IO #-}
  {-# SPECIALIZE instance NewFifo (SeqQueue (ST s) a) (ST s) #-}
  newFifo = do
    ref <- newMutVar Seq.empty
    return (SeqQueue ref)

instance PrimMonad m => Enqueue (SeqQueue m a) m a where
  {-# SPECIALIZE instance Enqueue (SeqQueue IO a) IO a #-}
  {-# SPECIALIZE instance Enqueue (SeqQueue (ST s) a) (ST s) a #-}
  enqueue (SeqQueue ref) val = do
    modifyMutVar ref (Seq.|> val)

instance PrimMonad m => Dequeue (SeqQueue m a) m a where
  {-# SPECIALIZE instance Dequeue (SeqQueue IO a) IO a #-}
  {-# SPECIALIZE instance Dequeue (SeqQueue (ST s) a) (ST s) a #-}

  dequeue (SeqQueue ref) = do
    s <- readMutVar ref
    case Seq.viewl s of
      Seq.EmptyL -> return Nothing
      val Seq.:< s' -> do
        writeMutVar ref s'
        return (Just val)

  dequeueBatch (SeqQueue ref) = do
    s <- readMutVar ref
    writeMutVar ref Seq.empty
    return (toList s)

instance PrimMonad m => QueueSize (SeqQueue m a) m where
  {-# SPECIALIZE instance QueueSize (SeqQueue IO a) IO #-}
  {-# SPECIALIZE instance QueueSize (SeqQueue (ST s) a) (ST s) #-}

  queueSize (SeqQueue ref) = do
    s <- readMutVar ref
    return $! Seq.length s

clear :: PrimMonad m => SeqQueue m a -> m ()
clear (SeqQueue ref) = do
  writeMutVar ref Seq.empty
