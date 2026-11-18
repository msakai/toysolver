{-# OPTIONS_HADDOCK show-extensions #-}
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
import Control.Monad.Primitive
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Data.Either
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Primitive.MutVar
import Data.Set (Set)
import qualified Data.Set as Set

import qualified ToySolver.Internal.Data.Vec as Vec
import ToySolver.EUF.CongruenceClosure (FSym, Term (..), ConstrID, VAFun (..))
import ToySolver.EUF.CongruenceClosure (Model (..), Entity, EntityTuple, eval, evalAp)
import qualified ToySolver.EUF.CongruenceClosure as CC

data Solver s
  = Solver
  { svCCSolver :: !(CC.Solver s)
  , svDisequalities :: MutVar s (Map (Term, Term) (Maybe ConstrID))
  , svExplanation :: MutVar s IntSet
  , svBacktrackPoints :: !(Vec.Vec s (Map (Term, Term) ()))
  }

newSolver :: PrimMonad m => m (Solver (PrimState m))
newSolver = stToPrim $ do
  cc <- CC.newSolver
  deqs <- newMutVar Map.empty
  expl <- newMutVar undefined
  bp <- Vec.new

  let solver =
        Solver
        { svCCSolver = cc
        , svDisequalities = deqs
        , svExplanation = expl
        , svBacktrackPoints = bp
        }
  return solver

newFSym :: PrimMonad m => Solver (PrimState m) -> m FSym
newFSym solver = CC.newFSym (svCCSolver solver)

newConst :: PrimMonad m => Solver (PrimState m) -> m Term
newConst solver = CC.newConst (svCCSolver solver)

newFun :: (PrimMonad m, CC.VAFun a) => Solver (PrimState m) -> m a
newFun solver = CC.newFun (svCCSolver solver)

assertEqual :: PrimMonad m => Solver (PrimState m) -> Term -> Term -> m ()
assertEqual solver t1 t2 = assertEqual' solver t1 t2 Nothing

assertEqual' :: PrimMonad m => Solver (PrimState m) -> Term -> Term -> Maybe ConstrID -> m ()
assertEqual' solver t1 t2 cid = CC.merge' (svCCSolver solver) t1 t2 cid

assertNotEqual :: PrimMonad m => Solver (PrimState m) -> Term -> Term -> m ()
assertNotEqual solver t1 t2 = assertNotEqual' solver t1 t2 Nothing

assertNotEqual' :: PrimMonad m => Solver (PrimState m) -> Term -> Term -> Maybe ConstrID -> m ()
assertNotEqual' solver t1 t2 cid = stToPrim $ if t1 < t2 then f (t1,t2) cid else f (t2,t1) cid
  where
    f deq cid = do
      ds <- readMutVar (svDisequalities solver)
      unless (deq `Map.member` ds) $ do
        _ <- termToFSym solver (fst deq) -- It is important to name the term for model generation
        _ <- termToFSym solver (snd deq) -- It is important to name the term for model generation
        writeMutVar (svDisequalities solver) $! Map.insert deq cid ds
        lv <- getCurrentLevel solver
        unless (lv==0) $ do
          Vec.unsafeModify' (svBacktrackPoints solver) (lv - 1) $ Map.insert deq ()

check :: PrimMonad m => Solver (PrimState m) -> m Bool
check solver = stToPrim $ do
  ds <- readMutVar (svDisequalities solver)
  liftM isRight $ runExceptT $ forM_ (Map.toList ds) $ \((t1,t2), cid) -> do
    b <- lift $ CC.areCongruent (svCCSolver solver) t1 t2
    if b then do      
      ret <- lift $ CC.explain (svCCSolver solver) t1 t2
      case ret of
        Nothing -> error "should not happen"
        Just cs -> do
          lift $ writeMutVar (svExplanation solver) $!
            case cid of
              Nothing -> cs
              Just c -> IntSet.insert c cs
      throwE ()
    else
      return ()

areEqual :: PrimMonad m => Solver (PrimState m) -> Term -> Term -> m Bool
areEqual solver t1 t2 = CC.areCongruent (svCCSolver solver) t1 t2

explain :: PrimMonad m => Solver (PrimState m) -> Maybe (Term,Term) -> m IntSet
explain solver Nothing = stToPrim $ readMutVar (svExplanation solver)
explain solver (Just (t1,t2)) = stToPrim $ do
  ret <- CC.explain (svCCSolver solver) t1 t2
  case ret of
    Nothing -> error "ToySolver.EUF.EUFSolver.explain: should not happen"
    Just cs -> return cs

-- -------------------------------------------------------------------
-- Model construction
-- -------------------------------------------------------------------

getModel :: PrimMonad m => Solver (PrimState m) -> m Model
getModel = CC.getModel . svCCSolver

-- -------------------------------------------------------------------
-- Backtracking
-- -------------------------------------------------------------------

type Level = Int

getCurrentLevel :: PrimMonad m => Solver (PrimState m) -> m Level
getCurrentLevel solver = Vec.getSize (svBacktrackPoints solver)

pushBacktrackPoint :: PrimMonad m => Solver (PrimState m) -> m ()
pushBacktrackPoint solver = stToPrim $ do
  CC.pushBacktrackPoint (svCCSolver solver)
  Vec.push (svBacktrackPoints solver) Map.empty

popBacktrackPoint :: PrimMonad m => Solver (PrimState m) -> m ()
popBacktrackPoint solver = stToPrim $ do
  lv <- getCurrentLevel solver
  if lv==0 then
    error "ToySolver.EUF.EUFSolver.popBacktrackPoint: root level"
  else do
    CC.popBacktrackPoint (svCCSolver solver)
    xs <- Vec.unsafePop (svBacktrackPoints solver)
    modifyMutVar' (svDisequalities solver) $ (`Map.difference` xs)

termToFlatTerm :: PrimMonad m => Solver (PrimState m) -> Term -> m CC.FlatTerm
termToFlatTerm = CC.termToFlatTerm . svCCSolver

termToFSym :: PrimMonad m => Solver (PrimState m) -> Term -> m FSym
termToFSym = CC.termToFSym . svCCSolver

fsymToTerm :: PrimMonad m => Solver (PrimState m) -> FSym -> m Term
fsymToTerm = CC.fsymToTerm . svCCSolver

fsymToFlatTerm :: PrimMonad m => Solver (PrimState m) -> FSym -> m CC.FlatTerm
fsymToFlatTerm = CC.fsymToFlatTerm . svCCSolver

flatTermToFSym :: PrimMonad m => Solver (PrimState m) -> CC.FlatTerm -> m FSym
flatTermToFSym = CC.flatTermToFSym . svCCSolver
