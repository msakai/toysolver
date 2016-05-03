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
import Data.Set
import qualified Data.Set as Set
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

prop_minimumCardinalityEdgeCover =
  forAll (arbitrarySmallIntSet 4) $ \as ->
    forAll (arbitrarySmallIntSet 4) $ \bs ->
      forAll (arbitrarySubsetOf [(a,b) | a <- IntSet.toList as, b <- IntSet.toList bs]) $ \es ->
        let isEdgeCover cs =
              IntSet.fromList [a | (a,_) <- Set.toList cs] == as &&
              IntSet.fromList [b | (_,b) <- Set.toList cs] == bs
        in case minimumCardinalityEdgeCover as bs es of
             Nothing -> 
               and [not (isEdgeCover cs') | cs' <- fmap Set.fromList $ subsetsOf es]
             Just cs ->
               isEdgeCover cs &&
               and [not (isEdgeCover cs') || Set.size cs <= Set.size cs' | cs' <- fmap Set.fromList $ subsetsOf es]

subsetsOf :: [a] -> [[a]]
subsetsOf [] = [[]]
subsetsOf (x:xs) = do
  ys <- subsetsOf xs
  [ys, x:ys]

arbitrarySubsetOf :: [a] -> Gen [a]
arbitrarySubsetOf [] = return []
arbitrarySubsetOf (x:xs) = do
  ys <- arbitrarySubsetOf xs
  b <- arbitrary
  if b then
    return ys
  else
    return (x:ys)

arbitrarySmallIntSet :: Int -> Gen IntSet
arbitrarySmallIntSet maxCard = do
  nX <- choose (0,maxCard)
  liftM IntSet.fromList $ replicateM nX $ arbitrary

arbitraryWeight :: (Arbitrary w) => IntSet -> IntSet -> Gen (Map (Int, Int) w)
arbitraryWeight as bs =
  liftM Map.unions $ forM (IntSet.toList as) $ \a -> do
    liftM Map.fromList $ forM (IntSet.toList bs) $ \b -> do
      w <- arbitrary
      return ((a,b),w)

bipartiteMatchingTestGroup :: TestTree
bipartiteMatchingTestGroup = $(testGroupGenerator)
