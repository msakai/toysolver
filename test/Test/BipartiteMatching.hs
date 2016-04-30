{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Test.BipartiteMatching (bipartiteMatchingTestGroup) where

import Control.Monad
import qualified Data.Foldable as F
import Data.Hashable
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map, (!))
import qualified Data.Map as Map
import ToySolver.Combinatorial.BipartiteMatching

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH

prop_minimumWeightPerfectMatching =
  forAll (choose (0,10)) $ \n ->
    let as = IntSet.fromList [1..n]
    in forAll (arbitraryWeight as as) $ \(w' :: Map (Int,Int) Rational) ->
         let w a b = w' ! (a,b)
             (obj, m, (ysA,ysB)) = minimumWeightPerfectMatchingComplete as as w
         in obj == sum [w a b | (a,b) <- IntMap.toList m] &&
            obj == F.sum ysA + F.sum ysB &&
            and [ya + yb <= w a b | (a,ya) <- IntMap.toList ysA, (b,yb) <- IntMap.toList ysB] &&
            IntMap.size m == n

prop_maximumWeightPerfectMatching =
  forAll (choose (0,10)) $ \n ->
    let as = IntSet.fromList [1..n]
    in forAll (arbitraryWeight as as) $ \(w' :: Map (Int,Int) Rational) ->
         let w a b = w' ! (a,b)
             (obj, m, (ysA,ysB)) = maximumWeightPerfectMatchingComplete as as w
         in obj == sum [w a b | (a,b) <- IntMap.toList m] &&
            obj == F.sum ysA + F.sum ysB &&
            and [ya + yb >= w a b | (a,ya) <- IntMap.toList ysA, (b,yb) <- IntMap.toList ysB] &&
            IntMap.size m == n

arbitraryWeight :: (Arbitrary w) => IntSet -> IntSet -> Gen (Map (Int, Int) w)
arbitraryWeight as bs =
  liftM Map.unions $ forM (IntSet.toList as) $ \a -> do
    liftM Map.fromList $ forM (IntSet.toList bs) $ \b -> do
      w <- arbitrary
      return ((a,b),w)

bipartiteMatchingTestGroup :: TestTree
bipartiteMatchingTestGroup = $(testGroupGenerator)
