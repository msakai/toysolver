{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Combinatorial.HittingSet.Simple
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Combinatorial.HittingSet.Simple
  ( minimalHittingSets
  , enumMinimalHittingSets
  ) where

import Control.Monad
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import qualified Data.Set as Set
import ToySolver.Combinatorial.HittingSet.Util (maintainNoSupersets)

minimalHittingSets :: Set IntSet -> Set IntSet
minimalHittingSets = Set.fromList . minimalHittingSets' . Set.toList

enumMinimalHittingSets :: Set IntSet -> [IntSet]
enumMinimalHittingSets = nubOrd . minimalHittingSets' . Set.toList

minimalHittingSets' :: [IntSet] -> [IntSet]
minimalHittingSets' es = f es IntSet.empty
  where
    f :: [IntSet] -> IntSet -> [IntSet]
    f [] hs = return hs
    f es hs = do
      v <- IntSet.toList $ IntSet.unions es
      let hs' = IntSet.insert v hs
      e <- es
      guard $ v `IntSet.member` e
      let es' = propagateChoice es v e
      f es' hs'

propagateChoice :: [IntSet] -> Int -> IntSet -> [IntSet]
propagateChoice es v e = zs
  where
    xs = filter (v `IntSet.notMember`) es
    ys = map (IntSet.filter (v <) . (`IntSet.difference` e)) xs
    zs = maintainNoSupersets ys

nubOrd :: Ord a => [a] -> [a]
nubOrd = go Set.empty
  where
    go occurred (x:xs)
      | x `Set.member` occurred = go occurred xs
      | otherwise = x : go (Set.insert x occurred) xs
    go _ [] = []
