{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
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

prop_maximumCardinalityMatching =
  forAll (arbitrarySmallIntSet 7) $ \as ->
    forAll (arbitrarySmallIntSet 7) $ \bs ->
      forAll (arbitrarySubsetOf [(a,b) | a <- IntSet.toList as, b <- IntSet.toList bs]) $ \es ->
        let m = maximumCardinalityMatching as bs es
        in isMatching m &&
           and [not (isMatching m') || IntMap.size m >= IntMap.size m' | m' <- allMatchings as bs es]
  where
    isMatching m = IntSet.size (IntSet.fromList (IntMap.elems m)) == IntMap.size m

prop_maximumWeightMatching =
  forAll (arbitrarySmallIntSet 7) $ \as ->
    forAll (arbitrarySmallIntSet 7) $ \bs ->
      forAll (arbitraryWeight' as bs) $ \(w :: Map (Int,Int) Rational) ->
        let (obj, m) = maximumWeightMatching as bs [(a,b,w) | ((a,b),w) <- Map.toList w]
        in isMatching m &&
           obj == sum [w Map.! (a,b) | (a,b) <- IntMap.toList m] &&
           and [ not (isMatching m') || obj >= sum [w Map.! (a,b) | (a,b) <- IntMap.toList m']
               | m' <- allMatchings as bs (Map.keys w) ]
  where
    isMatching m = IntSet.size (IntSet.fromList (IntMap.elems m)) == IntMap.size m

prop_maximumWeightMatchingComplete =
  forAll (arbitrarySmallIntSet 7) $ \as ->
    forAll (arbitrarySmallIntSet 7) $ \bs ->
      forAll (arbitraryWeight as bs) $ \(w :: Map (Int,Int) Rational) ->
        let (obj, m) = maximumWeightMatchingComplete as bs (\a b -> w Map.! (a,b))
        in isMatching m &&
           obj == sum [w Map.! (a,b) | (a,b) <- IntMap.toList m] &&
           and [ not (isMatching m') || obj >= sum [w Map.! (a,b) | (a,b) <- IntMap.toList m']
               | m' <- allMatchings as bs (Map.keys w) ]
  where
    isMatching m = IntSet.size (IntSet.fromList (IntMap.elems m)) == IntMap.size m

case_minimumWeightPerfectMatchingComplete_1 = do
  obj @?= 8
  m @?= IntMap.fromList [(1,2), (3,4)]
  where
    (obj, m, _) = minimumWeightPerfectMatchingComplete as bs (\a b -> w Map.! (a,b))
    as = IntSet.fromList [1,3]
    bs = IntSet.fromList [2,4]
    w :: Map (Int,Int) Int
    w = Map.fromList [((1,2),5),((1,4),2),((3,2),9),((3,4),3)]

prop_minimumWeightPerfectMatchingComplete =
  forAll (choose (0,10)) $ \n ->
    let as = IntSet.fromList [1..n]
        bs = as
        isPerfectMatching m = IntMap.keysSet m == as && IntSet.fromList (IntMap.elems m) == bs
    in forAll (arbitraryWeight as bs) $ \(w' :: Map (Int,Int) Rational) ->
         let w a b = w' ! (a,b)
             (obj, m, (ysA,ysB)) = minimumWeightPerfectMatchingComplete as bs w
         in isPerfectMatching m &&
            obj == sum [w a b | (a,b) <- IntMap.toList m] &&
            obj == F.sum ysA + F.sum ysB &&
            and [ya + yb <= w a b | (a,ya) <- IntMap.toList ysA, (b,yb) <- IntMap.toList ysB]

prop_maximumWeightPerfectMatchingComplete =
  forAll (choose (0,10)) $ \n ->
    let as = IntSet.fromList [1..n]
        bs = as
        isPerfectMatching m = IntMap.keysSet m == as && IntSet.fromList (IntMap.elems m) == bs
    in forAll (arbitraryWeight as as) $ \(w' :: Map (Int,Int) Rational) ->
         let w a b = w' ! (a,b)
             (obj, m, (ysA,ysB)) = maximumWeightPerfectMatchingComplete as as w
         in isPerfectMatching m &&
            obj == sum [w a b | (a,b) <- IntMap.toList m] &&
            obj == F.sum ysA + F.sum ysB &&
            and [ya + yb >= w a b | (a,ya) <- IntMap.toList ysA, (b,yb) <- IntMap.toList ysB]

prop_minimumWeightPerfectMatching =
  forAll (arbitrarySmallIntSet 7) $ \as ->
    forAll (arbitrarySmallIntSet 7) $ \bs ->
      let isPerfectMatching m = IntMap.keysSet m == as && IntSet.fromList (IntMap.elems m) == bs
      in forAll (arbitraryWeight' as bs) $ \(w :: Map (Int,Int) Rational) ->
           case minimumWeightPerfectMatching as bs [(a,b,w) | ((a,b),w) <- Map.toList w] of
             Nothing ->
               and [not (isPerfectMatching m) | m <- allMatchings as bs (Map.keys w)]
             Just (obj, m, (ysA,ysB)) ->
               isPerfectMatching m &&
               obj == sum [w Map.! (a,b) | (a,b) <- IntMap.toList m] &&
               obj == F.sum ysA + F.sum ysB &&
               and [ case Map.lookup (a,b) w of
                       Nothing -> True
                       Just v -> ya + yb <= v
                   | (a,ya) <- IntMap.toList ysA, (b,yb) <- IntMap.toList ysB ] &&
               and [ not (isPerfectMatching m') || obj <= sum [w Map.! (a,b) | (a,b) <- IntMap.toList m']
                   | m' <- allMatchings as bs (Map.keys w) ]

prop_maximumWeightPerfectMatching =
  forAll (arbitrarySmallIntSet 7) $ \as ->
    forAll (arbitrarySmallIntSet 7) $ \bs ->
      let isPerfectMatching m = IntMap.keysSet m == as && IntSet.fromList (IntMap.elems m) == bs
      in forAll (arbitraryWeight' as bs) $ \(w :: Map (Int,Int) Rational) ->
           case maximumWeightPerfectMatching as bs [(a,b,w) | ((a,b),w) <- Map.toList w] of
             Nothing ->
               and [not (isPerfectMatching m) | m <- allMatchings as bs (Map.keys w)]
             Just (obj, m, (ysA,ysB)) ->
               isPerfectMatching m &&
               obj == sum [w Map.! (a,b) | (a,b) <- IntMap.toList m] &&
               obj == F.sum ysA + F.sum ysB &&
               and [ case Map.lookup (a,b) w of
                       Nothing -> True
                       Just v -> ya + yb >= v
                   | (a,ya) <- IntMap.toList ysA, (b,yb) <- IntMap.toList ysB ] &&
               and [ not (isPerfectMatching m') || obj >= sum [w Map.! (a,b) | (a,b) <- IntMap.toList m']
                   | m' <- allMatchings as bs (Map.keys w) ]

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

prop_minimumWeightEdgeCover =
  forAll (arbitrarySmallIntSet 4) $ \as ->
    forAll (arbitrarySmallIntSet 4) $ \bs ->
      forAll (arbitraryWeight' as bs) $ \(w :: Map (Int,Int) Rational) ->
        let es = Map.keys w
            isEdgeCover cs =
              IntSet.fromList [a | (a,_) <- Set.toList cs] == as &&
              IntSet.fromList [b | (_,b) <- Set.toList cs] == bs
            obj cs = sum [w Map.! (a,b) | (a,b) <- Set.toList cs]
        in case minimumWeightEdgeCover as bs [(a,b,w) | ((a,b),w) <- Map.toList w] of
             Nothing ->
               and [not (isEdgeCover cs') | cs' <- fmap Set.fromList $ subsetsOf es]
             Just cs ->
               isEdgeCover cs &&
               and [not (isEdgeCover cs') || obj cs <= obj cs' | cs' <- fmap Set.fromList $ subsetsOf es]

prop_minimumWeightEdgeCoverComplete =
  forAll (arbitrarySmallIntSet 4) $ \as ->
    forAll (arbitrarySmallIntSet 4) $ \bs ->
      forAll (arbitraryWeight as bs) $ \(w :: Map (Int,Int) Rational) ->
        let es = Map.keys w
            isEdgeCover cs =
              IntSet.fromList [a | (a,_) <- Set.toList cs] == as &&
              IntSet.fromList [b | (_,b) <- Set.toList cs] == bs
            obj cs = sum [w Map.! (a,b) | (a,b) <- Set.toList cs]
        in case minimumWeightEdgeCoverComplete as bs (\a b -> w Map.! (a,b)) of
             Nothing ->
               and [not (isEdgeCover cs') | cs' <- fmap Set.fromList $ subsetsOf es]
             Just cs ->
               isEdgeCover cs &&
               and [not (isEdgeCover cs') || obj cs <= obj cs' | cs' <- fmap Set.fromList $ subsetsOf es]

allMatchings :: IntSet -> IntSet -> [(Int,Int)] -> [IntMap Int]
allMatchings as bs es = loop (IntSet.toList as) IntSet.empty IntMap.empty
  where
    es2 = Map.fromListWith IntSet.union [(a, IntSet.singleton b) | (a,b) <- es]
    loop [] _ m = return m
    loop (a : as) bs' m = do
      b <- IntSet.toList (Map.findWithDefault IntSet.empty a es2 `IntSet.difference` bs')
      loop as (IntSet.insert b bs') (IntMap.insert a b m)

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

arbitraryWeight' :: (Arbitrary w) => IntSet -> IntSet -> Gen (Map (Int, Int) w)
arbitraryWeight' as bs =
  liftM Map.unions $ forM (IntSet.toList as) $ \a -> do
    liftM Map.unions $ forM (IntSet.toList bs) $ \b -> do
      x <- arbitrary
      if x then do
        w <- arbitrary
        return $ Map.singleton (a,b) w
      else
        return Map.empty

bipartiteMatchingTestGroup :: TestTree
bipartiteMatchingTestGroup = $(testGroupGenerator)
