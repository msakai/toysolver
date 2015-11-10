-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.EUF.EUFSolver
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  unstable
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.EUF.EUFSolver
  ( -- * The @Solver@ type
    Solver
  , newSolver

  -- * Problem description
  , FSym
  , Term (..)
  , ConstrID
  , newFSym
  , assertEqual
  , assertEqual'
  , assertNotEqual
  , assertNotEqual'

  -- * Query
  , check
  , areEqual

  -- * Explanation
  , explain
  ) where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Data.Either
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IORef

import ToySolver.EUF.CongruenceClosure (FSym, Term (..), ConstrID)
import qualified ToySolver.EUF.CongruenceClosure as CC

data Solver
  = Solver
  { svCCSolver :: !CC.Solver
  , svDisequalities :: IORef (Map (Term, Term) (Maybe ConstrID))
  , svExplanation :: IORef IntSet
  }

newSolver :: IO Solver
newSolver = do
  cc <- CC.newSolver
  deqs <- newIORef Map.empty
  expl <- newIORef undefined
  let solver = 
        Solver
        { svCCSolver = cc
        , svDisequalities = deqs
        , svExplanation = expl
        }
  return solver

newFSym :: Solver -> IO FSym
newFSym solver = CC.newFSym (svCCSolver solver)

assertEqual :: Solver -> Term -> Term -> IO ()
assertEqual solver t1 t2 = assertEqual' solver t1 t2 Nothing

assertEqual' :: Solver -> Term -> Term -> Maybe ConstrID -> IO ()
assertEqual' solver t1 t2 cid = CC.merge' (svCCSolver solver) t1 t2 cid

assertNotEqual :: Solver -> Term -> Term -> IO ()
assertNotEqual solver t1 t2 = assertNotEqual' solver t1 t2 Nothing

assertNotEqual' :: Solver -> Term -> Term -> Maybe ConstrID -> IO ()
assertNotEqual' solver t1 t2 cid = if t1 < t2 then f (t1,t2) cid else f (t2,t1) cid
  where
    f deq cid = do
      ds <- readIORef (svDisequalities solver)
      unless (deq `Map.member` ds) $
        writeIORef (svDisequalities solver) $! Map.insert deq cid ds

check :: Solver -> IO Bool
check solver = do
  ds <- readIORef (svDisequalities solver)
  liftM isRight $ runExceptT $ forM_ (Map.toList ds) $ \((t1,t2), cid) -> do
    b <- lift $ CC.areCongruent (svCCSolver solver) t1 t2
    if b then do
      Just cs <- lift $ CC.explain (svCCSolver solver) t1 t2
      lift $ writeIORef (svExplanation solver) $!
        case cid of
          Nothing -> cs
          Just c -> IntSet.insert c cs
      throwE ()
    else
      return ()

areEqual :: Solver -> Term -> Term -> IO Bool
areEqual solver t1 t2 = CC.areCongruent (svCCSolver solver) t1 t2

explain :: Solver -> Maybe (Term,Term) -> IO IntSet
explain solver Nothing = readIORef (svExplanation solver)
explain solver (Just (t1,t2)) = do
  ret <- CC.explain (svCCSolver solver) t1 t2
  case ret of
    Nothing -> error "ToySolver.EUF.EUFSolver.explain: should not happen"
    Just cs -> return cs
