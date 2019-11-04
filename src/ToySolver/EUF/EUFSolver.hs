{-# LANGUAGE CPP #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.EUF.EUFSolver
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  unstable
-- Portability :  non-portable
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
  , VAFun (..)
  , newFSym
  , newFun
  , newConst
  , assertEqual
  , assertEqual'
  , assertNotEqual
  , assertNotEqual'

  -- * Query
  , check
  , areEqual

  -- * Explanation
  , explain

  -- * Model Construction
  , Entity
  , EntityTuple
  , Model (..)
  , getModel
  , eval
  , evalAp

  -- * Backtracking
  , pushBacktrackPoint
  , popBacktrackPoint

  -- * Low-level operations
  , termToFlatTerm
  , termToFSym
  , fsymToTerm
  , fsymToFlatTerm
  , flatTermToFSym
  ) where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Data.Either
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.IORef

import qualified ToySolver.Internal.Data.Vec as Vec
import ToySolver.EUF.CongruenceClosure (FSym, Term (..), ConstrID, VAFun (..))
import ToySolver.EUF.CongruenceClosure (Model (..), Entity, EntityTuple, eval, evalAp)
import qualified ToySolver.EUF.CongruenceClosure as CC

data Solver
  = Solver
  { svCCSolver :: !CC.Solver
  , svDisequalities :: IORef (Map (Term, Term) (Maybe ConstrID))
  , svExplanation :: IORef IntSet
  , svBacktrackPoints :: !(Vec.Vec (Map (Term, Term) ()))
  }

newSolver :: IO Solver
newSolver = do
  cc <- CC.newSolver
  deqs <- newIORef Map.empty
  expl <- newIORef undefined
  bp <- Vec.new

  let solver = 
        Solver
        { svCCSolver = cc
        , svDisequalities = deqs
        , svExplanation = expl
        , svBacktrackPoints = bp
        }
  return solver

newFSym :: Solver -> IO FSym
newFSym solver = CC.newFSym (svCCSolver solver)

newConst :: Solver -> IO Term
newConst solver = CC.newConst (svCCSolver solver)

newFun :: CC.VAFun a => Solver -> IO a
newFun solver = CC.newFun (svCCSolver solver)

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
      unless (deq `Map.member` ds) $ do
        _ <- termToFSym solver (fst deq) -- It is important to name the term for model generation
        _ <- termToFSym solver (snd deq) -- It is important to name the term for model generation
        writeIORef (svDisequalities solver) $! Map.insert deq cid ds
        lv <- getCurrentLevel solver
        unless (lv==0) $ do
          Vec.unsafeModify' (svBacktrackPoints solver) (lv - 1) $ Map.insert deq ()

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

-- -------------------------------------------------------------------
-- Model construction
-- -------------------------------------------------------------------

getModel :: Solver -> IO Model
getModel = CC.getModel . svCCSolver

-- -------------------------------------------------------------------
-- Backtracking
-- -------------------------------------------------------------------

type Level = Int

getCurrentLevel :: Solver -> IO Level
getCurrentLevel solver = Vec.getSize (svBacktrackPoints solver)

pushBacktrackPoint :: Solver -> IO ()
pushBacktrackPoint solver = do
  CC.pushBacktrackPoint (svCCSolver solver)
  Vec.push (svBacktrackPoints solver) Map.empty

popBacktrackPoint :: Solver -> IO ()
popBacktrackPoint solver = do
  lv <- getCurrentLevel solver
  if lv==0 then
    error "ToySolver.EUF.EUFSolver.popBacktrackPoint: root level"
  else do
    CC.popBacktrackPoint (svCCSolver solver)
    xs <- Vec.unsafePop (svBacktrackPoints solver)
    modifyIORef' (svDisequalities solver) $ (`Map.difference` xs)

termToFlatTerm = CC.termToFlatTerm . svCCSolver
termToFSym     = CC.termToFSym     . svCCSolver
fsymToTerm     = CC.fsymToTerm     . svCCSolver
fsymToFlatTerm = CC.fsymToFlatTerm . svCCSolver
flatTermToFSym = CC.flatTermToFSym . svCCSolver
