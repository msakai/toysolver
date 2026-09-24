{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}

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
import Data.IORef
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU

import ToySolver.EUF.CongruenceClosure (FSym, Term (..), VAFun (..))
import qualified ToySolver.Internal.Data.Vec as Vec


type NodeID = Int

type Sig = (FSym, VU.Vector NodeID)

data Solver
  = Solver
  {
  -- core union-find
    svParent :: !(Vec.Vec NodeID)

  -- structural info for every node (root or not)
  , svRepr :: !(Vec.Vec (FSym, VU.Vector NodeID))

  -- auxiliary info that is only valid for root nodes
  , svUseList :: !(Vec.Vec (Vec.UVec NodeID))
  , svMembers :: !(Vec.Vec (Vec.UVec NodeID))

  -- signature -> representative application node (need not be a root)
  , svSigTable :: !(IORef (Map Sig NodeID))

  -- for hash-consing: original Term object -> node id
  , svNodeOf :: !(IORef (Map Term NodeID))

  , svPending :: !(Vec.Vec (NodeID, NodeID))

  , svSymCounter :: IORef Int
  }

newSolver :: IO Solver
newSolver = do
  parent <- Vec.new
  repr <- Vec.new
  useList <- Vec.new
  members <- Vec.new
  sigTable <- newIORef Map.empty
  nodeOf <- newIORef Map.empty
  pending <- Vec.new
  counter <- newIORef 0
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

newFSym :: Solver -> IO FSym
newFSym solver = do
  n <- readIORef (svSymCounter solver)
  writeIORef (svSymCounter solver) $! n + 1
  return n

newFun :: VAFun a => Solver -> IO a
newFun solver = do
  c <- newFSym solver
  return $ withVArgs (TApp c)

newConst :: Solver -> IO Term
newConst = newFun

addTerm :: Solver -> Term -> IO NodeID
addTerm solver term@(TApp f args) = do
  nodeOf <- readIORef (svNodeOf solver)
  case Map.lookup term nodeOf of
    Just node -> pure node
    Nothing -> do
      argNodes <- mapM (addTerm solver) args
      node <- newNode solver f argNodes
      modifyIORef' (svNodeOf solver) (Map.insert term node)
      propagate solver
      pure node

newNode :: Solver -> FSym -> [NodeID] -> IO NodeID
newNode solver f args = do
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
    sigTable <- readIORef (svSigTable solver)
    case Map.lookup sig sigTable of
      Nothing -> writeIORef (svSigTable solver) $! Map.insert sig node sigTable
      Just node' -> Vec.push (svPending solver) (node, node')

  pure node

signature :: Solver -> NodeID -> IO Sig
signature solver node = do
  (f, args) <- Vec.read (svRepr solver) node
  args' <- VG.mapM (find solver) args
  pure (f, args')

-- ------------------------------------------------------------------
-- union-find core
-- ------------------------------------------------------------------

representative :: Solver -> NodeID -> IO NodeID
representative = find

find :: Solver -> NodeID -> IO NodeID
find solver x = do
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

areCongruent :: Solver -> Term -> Term -> IO Bool
areCongruent solver a b = do
  a' <- addTerm solver a
  b' <- addTerm solver b
  areCongruentNodes solver a' b'

areCongruentNodes :: Solver -> NodeID -> NodeID -> IO Bool
areCongruentNodes solver a b = do
  a' <- find solver a
  b' <- find solver b
  pure $ a' == b'

classMembers :: Solver -> NodeID -> IO IntSet
classMembers solver x = do
  x' <- find solver x
  mx <- Vec.read (svMembers solver) x'
  IntSet.fromList <$> Vec.getElems mx

-- ------------------------------------------------------------------
-- Merging an equation (entry point for asserting a = b from outside)
-- ------------------------------------------------------------------

merge :: Solver -> Term -> Term -> IO ()
merge solver a b = do
  a' <- addTerm solver a
  b' <- addTerm solver b
  mergeNodes solver a' b'

mergeNodes :: Solver -> NodeID -> NodeID -> IO ()
mergeNodes solver a b = do
  Vec.push (svPending solver) (a, b)
  propagate solver

propagate :: Solver -> IO ()
propagate solver = do
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
                  sigTable <- readIORef (svSigTable solver)
                  case Map.lookup sig sigTable of
                    Nothing -> writeIORef (svSigTable solver) $! Map.insert sig p sigTable
                    Just q -> Vec.push (svPending solver) (p, q)
                  loop
        loop

      propagate solver

-- ------------------------------------------------------------------
-- For debugging
-- ------------------------------------------------------------------

termOf :: Solver -> NodeID -> IO Term
termOf solver = worker
  where
    worker node = do
      (f, args) <- Vec.read (svRepr solver) node
      args' <- mapM worker (VG.toList args)
      pure (TApp f args')
