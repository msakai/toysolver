{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.HittingSet
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.HittingSet
  ( minimalHittingSets
  ) where

import Control.Monad
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List

type Vertex = Int
type HyperEdge = IntSet
type HittingSet = IntSet

-- FIXME: remove nub
minimalHittingSets :: [HyperEdge] -> [HittingSet]
minimalHittingSets es = nub $ f es IntSet.empty
  where
    f :: [HyperEdge] -> HittingSet -> [HittingSet]
    f [] hs = return hs
    f es hs = do
      v <- IntSet.toList $ IntSet.unions es
      let hs' = IntSet.insert v hs
      e <- es
      guard $ v `IntSet.member` e
      let es' = propagateChoice es v e
      f es' hs'

propagateChoice :: [HyperEdge] -> Vertex -> HyperEdge -> [HyperEdge]
propagateChoice es v e = zs
  where
    xs = filter (v `IntSet.notMember`) es
    ys = map (IntSet.filter (v <) . (`IntSet.difference` e)) xs
    zs = maintainNoSupersets ys

maintainNoSupersets :: [IntSet] -> [IntSet]
maintainNoSupersets xss = go [] xss
  where
    go yss [] = yss
    go yss (xs:xss) = go (xs : filter p yss) (filter p xss)
      where
        p zs = not (xs `IntSet.isSubsetOf` zs)
