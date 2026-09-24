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
import qualified Data.Foldable as F
import Data.IORef
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import ToySolver.EUF.CongruenceClosure (FSym, Term (..))
import qualified ToySolver.Internal.Data.Vec as Vec


type NodeID = Int

type Sig = (FSym, VU.Vector NodeID)

data Solver
  = Solver
  {
  -- core union-find
    svParent :: !(Vec.Vec NodeID)

  -- structural info for every node (root or not)
  , svFunc :: !(Vec.UVec FSym)
  , svArgs :: !(Vec.Vec (VU.Vector NodeID))

  -- auxiliary info that is only valid for root nodes
  , svUseList :: !(Vec.Vec (Seq NodeID))
  , svMembers :: !(Vec.Vec (Seq NodeID))

  -- signature -> representative application node (need not be a root)
  , svSigTable :: !(IORef (Map Sig NodeID))

  -- for hash-consing: original Term object -> node id
  , svNodeOf :: !(IORef (Map Term NodeID))

  , svPending :: !(Vec.Vec (NodeID, NodeID))
  }

newSolver :: IO Solver
newSolver = do
  parent <- Vec.new
  func <- Vec.new
  args <- Vec.new
  useList <- Vec.new
  members <- Vec.new
  sigTable <- newIORef Map.empty
  nodeOf <- newIORef Map.empty
  pending <- Vec.new
  pure $ Solver
    { svParent = parent
    , svFunc = func
    , svArgs = args
    , svUseList = useList
    , svMembers = members
    , svSigTable = sigTable
    , svNodeOf = nodeOf
    , svPending = pending
    }

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
  Vec.push (svUseList solver) Seq.empty
  Vec.push (svMembers solver) (Seq.singleton node)
  Vec.push (svFunc solver) f
  Vec.push (svArgs solver) (VG.fromList args)

  -- register this node in the use-list of each argument's current root
  forM_ args $ \a -> do
    ra <- find solver a
    Vec.modify' (svUseList solver) ra (node Seq.<|)

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
  f <- Vec.read (svFunc solver) node
  args <- Vec.read (svArgs solver) node
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
  (IntSet.fromList . F.toList) <$> Vec.read (svMembers solver) x'

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
        -- absorb the smaller class (rb) into the larger one (ra)
        (ra, rb, ma, mb) <-
          if Seq.length ma < Seq.length mb then
            pure (rb, ra, mb, ma)
          else
            pure (ra, rb, ma, mb)
        Vec.write (svParent solver) rb ra
        Vec.write (svMembers solver) ra (ma <> mb)
        -- This is the core DST trick: only rehash the use-list of
        -- the absorbed side (rb). The use-list on the ra side is
        -- untouched since its keys (root ids) haven't changed.
        moved <- Vec.read (svUseList solver) rb
        Vec.write (svUseList solver) rb Seq.empty
        Vec.modify' (svUseList solver) ra (<> moved)
        forM_ moved $ \p -> do
          sig <- signature solver p
          sigTable <- readIORef (svSigTable solver)
          case Map.lookup sig sigTable of
            Nothing -> writeIORef (svSigTable solver) $! Map.insert sig p sigTable
            Just q -> Vec.push (svPending solver) (p, q)
      propagate solver

-- ------------------------------------------------------------------
-- For debugging
-- ------------------------------------------------------------------

termOf :: Solver -> NodeID -> IO Term
termOf solver = worker
  where
    worker node = do
      f <- Vec.read (svFunc solver) node
      args <- Vec.read (svArgs solver) node
      args' <- mapM worker (VG.toList args)
      pure (TApp f args')
