{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.EUF.CongruenceClosure.DowneySethiTarjan
-- Copyright   :  (c) Masahiro Sakai 2026
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Downey-Sethi-Tarjan (1980) style congruence closure.
--
-- * no backtracking
--
-- * no explanation (proof) generation
--
-- * ground terms only (no variables / E-matching)
--
-- Translated from <https://github.com/msakai/sandbox/blob/9f75ae38ba6e1bb04ecc5b4fbe558d9347d613f7/congruence_closure.py>.
--
-----------------------------------------------------------------------------
module ToySolver.EUF.CongruenceClosure.DowneySethiTarjan
  (

  -- * Problem description
    FSym
  , Term (..)

  -- * The @Solver@ type
  , Solver (..)
  , newSolver

  -- * Introduction of new symbols
  , newFSym
  , newFun
  , newConst

  -- * Registering a term (builds internal nodes with hash-consing)
  , NodeID
  , addTerm

  -- * Union-find core
  , representative
  , areCongruent
  , areCongruentNodes
  , classMembers

  -- * Merging an equation
  , merge
  , mergeNodes

  -- * For debugging
  , termOf
  ) where

import Control.Monad
import Control.Monad.Primitive
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Primitive.MutVar
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU

import ToySolver.EUF.CongruenceClosure.Base
import qualified ToySolver.Internal.Data.Vec as Vec


type NodeID = Int

type Sig = (FSym, VU.Vector NodeID)

data Solver s
  = Solver
  {
  -- core union-find
    svParent :: !(Vec.Vec s NodeID)

  -- structural info for every node (root or not)
  , svRepr :: !(Vec.Vec s (FSym, VU.Vector NodeID))

  -- auxiliary info that is only valid for root nodes
  , svUseList :: !(Vec.Vec s (Vec.UVec s NodeID))
  , svMembers :: !(Vec.Vec s (Vec.UVec s NodeID))

  -- signature -> representative application node (need not be a root)
  , svSigTable :: !(MutVar s (Map Sig NodeID))

  -- for hash-consing: original Term object -> node id
  , svNodeOf :: !(MutVar s (Map Term NodeID))

  , svPending :: !(Vec.Vec s (NodeID, NodeID))

  , svSymCounter :: MutVar s Int
  }

newSolver :: PrimMonad m => m (Solver (PrimState m))
newSolver = stToPrim $ do
  parent <- Vec.new
  repr <- Vec.new
  useList <- Vec.new
  members <- Vec.new
  sigTable <- newMutVar Map.empty
  nodeOf <- newMutVar Map.empty
  pending <- Vec.new
  counter <- newMutVar 0
  pure $ Solver
    { svParent = parent
    , svRepr = repr
    , svUseList = useList
    , svMembers = members
    , svSigTable = sigTable
    , svNodeOf = nodeOf
    , svPending = pending
    , svSymCounter = counter
    }

newFSym :: PrimMonad m => Solver (PrimState m) -> m FSym
newFSym solver = stToPrim $ do
  n <- readMutVar (svSymCounter solver)
  writeMutVar (svSymCounter solver) $! n + 1
  return n

newFun :: (PrimMonad m, VAFun a) => Solver (PrimState m) -> m a
newFun solver = stToPrim $ do
  c <- newFSym solver
  return $ withVArgs (TApp c)

newConst :: PrimMonad m => Solver (PrimState m) -> m Term
newConst = newFun

addTerm :: PrimMonad m => Solver (PrimState m) -> Term -> m NodeID
addTerm solver term@(TApp f args) = stToPrim $ do
  nodeOf <- readMutVar (svNodeOf solver)
  case Map.lookup term nodeOf of
    Just node -> pure node
    Nothing -> do
      argNodes <- mapM (addTerm solver) args
      node <- newNode solver f argNodes
      modifyMutVar' (svNodeOf solver) (Map.insert term node)
      propagate solver
      pure node

newNode :: PrimMonad m => Solver (PrimState m) -> FSym -> [NodeID] -> m NodeID
newNode solver f args = stToPrim $ do
  node <- Vec.getSize (svParent solver)
  Vec.push (svParent solver) node
  Vec.push (svUseList solver) =<< Vec.new
  Vec.push (svMembers solver) =<< (Vec.new >>= \m -> Vec.push m node >> pure m)
  Vec.push (svRepr solver) (f, VG.fromList args)

  -- register this node in the use-list of each argument's current root
  forM_ args $ \a -> do
    ra <- find solver a
    ua <- Vec.read (svUseList solver) ra
    Vec.push ua node

  -- for an application node, compute its signature and check for a collision
  unless (null args) $ do
    sig <- signature solver node
    sigTable <- readMutVar (svSigTable solver)
    case Map.lookup sig sigTable of
      Nothing -> writeMutVar (svSigTable solver) $! Map.insert sig node sigTable
      Just node' -> Vec.push (svPending solver) (node, node')

  pure node

signature :: PrimMonad m => Solver (PrimState m) -> NodeID -> m Sig
signature solver node = stToPrim $ do
  (f, args) <- Vec.read (svRepr solver) node
  args' <- VG.mapM (find solver) args
  pure (f, args')

-- ------------------------------------------------------------------
-- union-find core
-- ------------------------------------------------------------------

representative :: PrimMonad m => Solver (PrimState m) -> NodeID -> m NodeID
representative = find

find :: PrimMonad m => Solver (PrimState m) -> NodeID -> m NodeID
find solver x = stToPrim $ do
  let findRoot root = do
        root' <- Vec.read (svParent solver) root
        if root /= root' then do
          findRoot root'
        else do
          pure root
  root <- findRoot x
  let compressPath y = do
        z <- Vec.read (svParent solver) y
        if z /= root then do
          Vec.write (svParent solver) y root
          compressPath z
        else
          pure ()
  compressPath x
  pure root

areCongruent :: PrimMonad m => Solver (PrimState m) -> Term -> Term -> m Bool
areCongruent solver a b = stToPrim $ do
  a' <- addTerm solver a
  b' <- addTerm solver b
  areCongruentNodes solver a' b'

areCongruentNodes :: PrimMonad m => Solver (PrimState m) -> NodeID -> NodeID -> m Bool
areCongruentNodes solver a b = stToPrim $ do
  a' <- find solver a
  b' <- find solver b
  pure $ a' == b'

classMembers :: PrimMonad m => Solver (PrimState m) -> NodeID -> m IntSet
classMembers solver x = stToPrim $ do
  x' <- find solver x
  mx <- Vec.read (svMembers solver) x'
  IntSet.fromList <$> Vec.getElems mx

-- ------------------------------------------------------------------
-- Merging an equation (entry point for asserting a = b from outside)
-- ------------------------------------------------------------------

merge :: PrimMonad m => Solver (PrimState m) -> Term -> Term -> m ()
merge solver a b = stToPrim $ do
  a' <- addTerm solver a
  b' <- addTerm solver b
  mergeNodes solver a' b'

mergeNodes :: PrimMonad m => Solver (PrimState m) -> NodeID -> NodeID -> m ()
mergeNodes solver a b = stToPrim $ do
  Vec.push (svPending solver) (a, b)
  propagate solver

propagate :: PrimMonad m => Solver (PrimState m) -> m ()
propagate solver = stToPrim $ do
  m <- Vec.popMaybe (svPending solver)
  case m of
    Nothing -> pure ()
    Just (a, b) -> do
      ra <- find solver a
      rb <- find solver b
      unless (ra == rb) $ do
        ma <- Vec.read (svMembers solver) ra
        mb <- Vec.read (svMembers solver) rb
        sa <- Vec.getSize ma
        sb <- Vec.getSize mb
        (ra, rb, ma, mb, _sa, sb) <-
          if sa < sb then
            pure (rb, ra, mb, ma, sb, sa)
          else
            pure (ra, rb, ma, mb, sa, sb)

        -- absorb the smaller class (rb) into the larger one (ra)
        Vec.write (svParent solver) rb ra
        forM_ [0..sb-1] $ \i -> do
          x <- Vec.read mb i
          Vec.push ma x
        Vec.clear mb

        -- This is the core DST trick: only rehash the use-list of
        -- the absorbed side (rb). The use-list on the ra side is
        -- untouched since its keys (root ids) haven't changed.
        ua <- Vec.read (svUseList solver) ra
        ub <- Vec.read (svUseList solver) rb
        let loop = do
              ret <- Vec.popMaybe ub
              case ret of
                Nothing -> pure ()
                Just p -> do
                  Vec.push ua p
                  sig <- signature solver p
                  sigTable <- readMutVar (svSigTable solver)
                  case Map.lookup sig sigTable of
                    Nothing -> writeMutVar (svSigTable solver) $! Map.insert sig p sigTable
                    Just q -> Vec.push (svPending solver) (p, q)
                  loop
        loop

      propagate solver

-- ------------------------------------------------------------------
-- For debugging
-- ------------------------------------------------------------------

termOf :: PrimMonad m => Solver (PrimState m) -> NodeID -> m Term
termOf solver x = stToPrim $ worker x
  where
    worker node = do
      (f, args) <- Vec.read (svRepr solver) node
      args' <- mapM worker (VG.toList args)
      pure (TApp f args')
