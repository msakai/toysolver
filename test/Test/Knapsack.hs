{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.Knapsack (knapsackTestGroup) where

import Control.Monad
import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified ToySolver.Combinatorial.Knapsack.BB as KnapsackBB
import qualified ToySolver.Combinatorial.Knapsack.DPDense as KnapsackDPDense
import qualified ToySolver.Combinatorial.Knapsack.DPSparse as KnapsackDPSparse

-- ---------------------------------------------------------------------
-- Knapsack problems

case_knapsack_BB_1 :: Assertion
case_knapsack_BB_1 = KnapsackBB.solve [(5,4), (6,5), (3,2)] 9 @?= (11, 9, [True,True,False])

case_knapsack_BB_2 :: Assertion
case_knapsack_BB_2 = KnapsackBB.solve [(16,2), (19,3), (23,4), (28,5)] 7 @?= (44, 7, [True,False,False,True])

case_knapsack_DPDense_1 :: Assertion
case_knapsack_DPDense_1 = KnapsackDPDense.solve [(5,4), (6,5), (3,2)] 9 @?= (11, 9, [True,True,False])

case_knapsack_DPDense_2 :: Assertion
case_knapsack_DPDense_2 = KnapsackDPDense.solve [(16,2), (19,3), (23,4), (28,5)] 7 @?= (44, 7, [True,False,False,True])

prop_knapsack_DPDense_equals_BB :: Property
prop_knapsack_DPDense_equals_BB =
  forAll knapsackProblems $ \(items,lim) ->
    let items' = [(v, fromIntegral w) | (v,w) <- items]
        lim' = fromIntegral lim
        (v1,_,_) = KnapsackBB.solve items' lim'
        (v2,_,_) = KnapsackDPDense.solve items lim
    in v1 === v2

case_knapsack_DPSparse_1 :: Assertion
case_knapsack_DPSparse_1 = KnapsackDPSparse.solve [(5::Int,4::Int), (6,5), (3,2)] 9 @?= (11, 9, [True,True,False])

case_knapsack_DPSparse_2 :: Assertion
case_knapsack_DPSparse_2 = KnapsackDPSparse.solve [(16::Int,2::Int), (19,3), (23,4), (28,5)] 7 @?= (44, 7, [True,False,False,True])

prop_knapsack_DPSparse_equals_BB :: Property
prop_knapsack_DPSparse_equals_BB =
  forAll knapsackProblems $ \(items,lim) ->
    let -- items' :: Num a => [(Rational, a)]
        items' = [(v, fromIntegral w) | (v,w) <- items]
        (v1,_,_) = KnapsackBB.solve items' (fromIntegral lim)
        (v2,_,_) = KnapsackDPSparse.solve items' (fromIntegral lim)
    in v1 === v2

knapsackProblems :: Gen ([(KnapsackDPDense.Value, KnapsackDPDense.Weight)], KnapsackDPDense.Weight)
knapsackProblems = do
  lim <- choose (0,30)
  items <- listOf $ do
    v <- liftM abs arbitrary
    w <- choose (0,30)
    return (v,w)
  return (items, lim)

------------------------------------------------------------------------
-- Test harness

knapsackTestGroup :: TestTree
knapsackTestGroup = $(testGroupGenerator)
