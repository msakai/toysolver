{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.PBO.Context
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.SAT.PBO.Context
  ( Context (..)
  , getBestValue
  , getBestModel
  , isOptimum
  , isFinished
  , getSearchUpperBound
  , setFinished

  , SimpleContext
  , newSimpleContext
  , newSimpleContext2
  , setOnUpdateBestSolution
  , setOnUpdateLowerBound
  , setLogger

  , Normalized
  , normalize
  ) where

import Control.Monad
import Control.Concurrent.STM
import Data.IORef
import Data.Maybe
import qualified ToySolver.SAT.Types as SAT

{--------------------------------------------------------------------
  Context class
--------------------------------------------------------------------}

class Context a where
  getObjectiveFunction :: a -> SAT.PBLinSum
  evalObjectiveFunction :: a -> SAT.Model -> Integer

  isUnsat         :: a -> STM Bool
  getBestSolution :: a -> STM (Maybe (SAT.Model, Integer))
  getLowerBound   :: a -> STM Integer

  setUnsat      :: a -> IO ()
  addSolution   :: a -> SAT.Model -> IO ()
  addLowerBound :: a -> Integer -> IO ()
  logMessage    :: a -> String -> IO ()

  evalObjectiveFunction c m = SAT.evalPBLinSum m (getObjectiveFunction c)

getBestValue :: Context a => a -> STM (Maybe Integer)
getBestValue cxt = liftM (fmap snd) $ getBestSolution cxt

getBestModel :: Context a => a -> STM (Maybe SAT.Model)
getBestModel cxt = liftM (fmap fst) $ getBestSolution cxt

isOptimum :: Context a => a -> STM Bool
isOptimum cxt = do
  ub <- getBestValue cxt
  lb <- getLowerBound cxt
  case ub of
    Nothing -> return False
    Just val -> return $ val <= lb
    -- Note that solving with the assumption 'obj < val' can yield
    -- a lower bound that is higher than val!

isFinished :: Context a => a -> STM Bool
isFinished cxt = do
  b1 <- isUnsat cxt
  b2 <- isOptimum cxt
  return $ b1 || b2

getSearchUpperBound :: Context a => a -> STM Integer
getSearchUpperBound ctx = do
  ret <- getBestValue ctx
  case ret of
    Just val -> return $ val - 1
    Nothing -> return $ SAT.pbLinUpperBound $ getObjectiveFunction ctx

setFinished :: Context a => a -> IO ()
setFinished cxt = do
  join $ atomically $ do
    ret <- getBestValue cxt
    case ret of
      Just val -> return $ addLowerBound cxt val
      Nothing -> return $ setUnsat cxt

{--------------------------------------------------------------------
  Simple Context
--------------------------------------------------------------------}

data SimpleContext
  = SimpleContext
  { scGetObjectiveFunction :: SAT.PBLinSum
  , scEvalObjectiveFunction :: SAT.Model -> Integer

  , scUnsatRef        :: TVar Bool
  , scBestSolutionRef :: TVar (Maybe (SAT.Model, Integer))
  , scLowerBoundRef   :: TVar Integer

  , scOnUpdateBestSolutionRef :: IORef (SAT.Model -> Integer -> IO ())
  , scOnUpdateLowerBoundRef   :: IORef (Integer -> IO ())
  , scLoggerRef               :: IORef (String -> IO ())
  }

instance Context SimpleContext where
  getObjectiveFunction = scGetObjectiveFunction
  evalObjectiveFunction = scEvalObjectiveFunction

  isUnsat sc = readTVar (scUnsatRef sc)
  getBestSolution sc = readTVar (scBestSolutionRef sc)
  getLowerBound sc = readTVar (scLowerBoundRef sc)

  setUnsat sc = do
    atomically $ do
      sol <- getBestSolution sc
      unless (isNothing sol) $ error "setUnsat: already has a solution" -- FIXME: use throwSTM?
      writeTVar (scUnsatRef sc) True

  addSolution sc m = do
    let !val = evalObjectiveFunction sc m
    join $ atomically $ do
      unsat <- isUnsat sc
      when unsat $ error "addSolution: already marked as unsatisfiable" -- FIXME: use throwSTM?

      sol0 <- getBestValue sc
      case sol0 of
        Just val0 | val0 <= val -> return $ return ()
        _ -> do
          writeTVar (scBestSolutionRef sc) (Just (m, val))
          return $ do
            h <- readIORef (scOnUpdateBestSolutionRef sc)
            h m val

  addLowerBound sc lb = do
    join $ atomically $ do
      lb0 <- getLowerBound sc
      if lb <= lb0 then
        return $ return ()
      else do
        writeTVar (scLowerBoundRef sc) lb
        return $ do
          h <- readIORef (scOnUpdateLowerBoundRef sc)
          h lb

  logMessage sc msg = do
    h <- readIORef (scLoggerRef sc)
    h msg

newSimpleContext :: SAT.PBLinSum -> IO SimpleContext
newSimpleContext obj = newSimpleContext2 obj (\m -> SAT.evalPBLinSum m obj)

newSimpleContext2 :: SAT.PBLinSum -> (SAT.Model -> Integer) -> IO SimpleContext
newSimpleContext2 obj obj2 = do
  unsatRef <- newTVarIO False
  bestsolRef <- newTVarIO Nothing
  lbRef <- newTVarIO $! SAT.pbLinLowerBound obj

  onUpdateBestSolRef <- newIORef $ \_ _ -> return ()
  onUpdateLBRef <- newIORef $ \_ -> return ()
  loggerRef <- newIORef $ \_ -> return ()

  return $
    SimpleContext
    { scGetObjectiveFunction = obj
    , scEvalObjectiveFunction = obj2

    , scUnsatRef        = unsatRef
    , scBestSolutionRef = bestsolRef
    , scLowerBoundRef   = lbRef

    , scOnUpdateBestSolutionRef = onUpdateBestSolRef
    , scOnUpdateLowerBoundRef   = onUpdateLBRef
    , scLoggerRef               = loggerRef
    }

setOnUpdateBestSolution :: SimpleContext -> (SAT.Model -> Integer -> IO ()) -> IO ()
setOnUpdateBestSolution sc h = writeIORef (scOnUpdateBestSolutionRef sc) h

setOnUpdateLowerBound :: SimpleContext -> (Integer -> IO ()) -> IO ()
setOnUpdateLowerBound sc h = writeIORef (scOnUpdateLowerBoundRef sc) h

setLogger :: SimpleContext -> (String -> IO ()) -> IO ()
setLogger sc h = writeIORef (scLoggerRef sc) h

{--------------------------------------------------------------------
  Normalization
--------------------------------------------------------------------}

data Normalized a
  = Normalized
  { nBase :: a
  , nObjectiveFunction :: SAT.PBLinSum
  , nOffset :: Integer
  }

instance Context a => Context (Normalized a) where
  getObjectiveFunction = nObjectiveFunction

  evalObjectiveFunction cxt m = evalObjectiveFunction (nBase cxt) m - nOffset cxt

  isUnsat cxt = isUnsat (nBase cxt)

  getBestSolution cxt = do
    sol <- getBestSolution (nBase cxt)
    case sol of
      Nothing -> return Nothing
      Just (m, val) -> return $ Just (m, val - nOffset cxt)

  getLowerBound cxt = do
    lb <- getLowerBound (nBase cxt)
    return $ lb - nOffset cxt

  setUnsat cxt = setUnsat $ nBase cxt

  addSolution cxt m = do
    addSolution (nBase cxt) m

  addLowerBound cxt lb = do
    addLowerBound (nBase cxt) (lb + nOffset cxt)

  logMessage cxt msg = logMessage (nBase cxt) msg

normalize :: Context a => a -> Normalized a
normalize cxt = Normalized cxt obj' offset
  where
    obj = getObjectiveFunction cxt
    (obj',offset) = SAT.normalizePBLinSum (obj, 0)

