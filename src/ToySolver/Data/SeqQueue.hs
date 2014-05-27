{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.SeqQueue
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
module ToySolver.Data.SeqQueue
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

import Data.IORef
import Data.Queue
import Data.Foldable
import qualified Data.Sequence as Seq

newtype SeqQueue a = SeqQueue (IORef (Seq.Seq a))

instance NewFifo (SeqQueue a) IO where
  newFifo = do
    ref <- newIORef Seq.empty
    return (SeqQueue ref)

instance Enqueue (SeqQueue a) IO a where
  enqueue (SeqQueue ref) val = do
    modifyIORef ref (Seq.|> val)

instance Dequeue (SeqQueue a) IO a where
  dequeue (SeqQueue ref) = do
    s <- readIORef ref
    case Seq.viewl s of
      Seq.EmptyL -> return Nothing
      val Seq.:< s' -> do
        writeIORef ref s'
        return (Just val)

  dequeueBatch (SeqQueue ref) = do
    s <- readIORef ref
    writeIORef ref Seq.empty
    return (toList s)

instance QueueSize (SeqQueue a) IO where
  queueSize (SeqQueue ref) = do
    s <- readIORef ref
    return $! Seq.length s

clear :: SeqQueue a -> IO ()
clear (SeqQueue ref) = do
  writeIORef ref Seq.empty
