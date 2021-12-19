{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.SubsetSum (subsetSumTestGroup) where

import Control.Monad
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import Test.Tasty
import qualified Test.Tasty.QuickCheck as QC
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified ToySolver.Combinatorial.Knapsack.BB as KnapsackBB
import qualified ToySolver.Combinatorial.SubsetSum as SubsetSum

-- ---------------------------------------------------------------------
-- SubsetSum

evalSubsetSum :: [Integer] -> [Bool] -> Integer
evalSubsetSum ws bs = sum [w | (w,b) <- zip ws bs, b]

prop_maxSubsetSum_soundness :: Property
prop_maxSubsetSum_soundness =
  forAll arbitrary $ \c ->
    forAll arbitrary $ \ws ->
      case SubsetSum.maxSubsetSum (V.fromList ws) c of
        Just (obj, bs) -> obj === evalSubsetSum ws (VU.toList bs) QC..&&. obj <= c
        Nothing -> property True

prop_maxSubsetSum_completeness :: Property
prop_maxSubsetSum_completeness =
  forAll arbitrary $ \c ->
    forAll g $ \ws ->
      case SubsetSum.maxSubsetSum (V.fromList ws) c of
        Just (obj, bs) ->
          conjoin
          [ VU.length bs === length ws
          , obj === evalSubsetSum ws (VU.toList bs)
          , property $ obj <= c
          ]
        Nothing -> conjoin [counterexample (show bs) $ c < evalSubsetSum ws bs | bs <- replicateM (length ws) [False,True]]
  where
    g = do
      n <- choose (0,10)
      replicateM n arbitrary

prop_maxSubsetSum_isEqualToKnapsackBBSolver :: Property
prop_maxSubsetSum_isEqualToKnapsackBBSolver =
  forAll (liftM abs arbitrary) $ \c ->
    forAll (liftM (map abs) arbitrary) $ \ws ->
      let Just (obj1, _bs1) = SubsetSum.maxSubsetSum (V.fromList ws) c
          (obj2, _, _bs2) = KnapsackBB.solve [(fromIntegral w, fromIntegral w) | w <- ws] (fromIntegral c)
      in fromIntegral obj1 === obj2

case_maxSubsetSum_regression_test_1 :: Assertion
case_maxSubsetSum_regression_test_1 =
  SubsetSum.maxSubsetSum (V.fromList [4,28,5,6,18]) 25 @?= Just (24, VU.fromList [False,False,False,True,True])

case_maxSubsetSum_regression_test_2 :: Assertion
case_maxSubsetSum_regression_test_2 =
  SubsetSum.maxSubsetSum (V.fromList [10,15]) 18 @?= Just (15, VU.fromList [False,True])

prop_minSubsetSum_soundness :: Property
prop_minSubsetSum_soundness =
  forAll arbitrary $ \c ->
    forAll arbitrary $ \ws ->
      case SubsetSum.minSubsetSum (V.fromList ws) c of
        Just (obj, bs) -> obj === evalSubsetSum ws (VU.toList bs) QC..&&. c <= obj
        Nothing -> property True

prop_minSubsetSum_completeness :: Property
prop_minSubsetSum_completeness =
  forAll arbitrary $ \c ->
    forAll g $ \ws ->
      case SubsetSum.minSubsetSum (V.fromList ws) c of
        Just (obj, bs) ->
          conjoin
          [ VU.length bs === length ws
          , obj === evalSubsetSum ws (VU.toList bs)
          , property $ c <= obj
          ]
        Nothing -> conjoin [counterexample (show bs) $ evalSubsetSum ws bs < c | bs <- replicateM (length ws) [False,True]]
  where
    g = do
      n <- choose (0,10)
      replicateM n arbitrary

prop_subsetSum_soundness :: Property
prop_subsetSum_soundness =
  forAll arbitrary $ \c ->
    forAll arbitrary $ \ws ->
      case SubsetSum.subsetSum (V.fromList ws) c of
        Just bs -> VU.length bs === length ws QC..&&. evalSubsetSum ws (VU.toList bs) === c
        Nothing -> property True

prop_subsetSum_completeness :: Property
prop_subsetSum_completeness =
  forAll arbitrary $ \c ->
    forAll g $ \ws ->
      case SubsetSum.subsetSum (V.fromList ws) c of
        Just bs -> VU.length bs === length ws QC..&&. evalSubsetSum ws (VU.toList bs) === c
        Nothing -> conjoin [counterexample (show bs) $ c /= evalSubsetSum ws bs | bs <- replicateM (length ws) [False,True]]
  where
    g = do
      n <- choose (0,10)
      replicateM n arbitrary

------------------------------------------------------------------------
-- Test harness

subsetSumTestGroup :: TestTree
subsetSumTestGroup = $(testGroupGenerator)
