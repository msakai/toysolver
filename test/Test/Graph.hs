{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module Test.Graph (graphTestGroup) where

import Control.Monad
import Data.Array
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.Tasty.TH

import ToySolver.Graph.Base


-- ------------------------------------------------------------------------

arbitraryGraph :: Int -> Gen Graph
arbitraryGraph n = do
  m <- choose (0, n*n-1)
  fmap (graphFromUnorderedEdges n) $ replicateM m $ do
    node1 <- choose (0, n-1)
    node2 <- fmap (\i -> (node1 + i) `mod` n) $ choose (0, n-1)
    return (node1, node2, ())

arbitraryDiGraph :: Int -> Gen Graph
arbitraryDiGraph n = do
  m <- choose (0, n*n-1)
  fmap (graphFromEdges n) $ replicateM m $ do
    node1 <- choose (0, n-1)
    node2 <- fmap (\i -> (node1 + i) `mod` n) $ choose (0, n-1)
    return (node1, node2, ())

arbitrarySimpleGraph :: Int -> Gen Graph
arbitrarySimpleGraph n = do
  m <- choose (0, n*n-1)
  fmap (graphFromUnorderedEdges n) $ replicateM m $ do
    node1 <- choose (0, n-1)
    node2 <- fmap (\i -> (node1 + i) `mod` n) $ choose (1, n-1)
    return (node1, node2, ())

vertexes :: EdgeLabeledGraph a -> IntSet
vertexes = IntSet.fromAscList . uncurry enumFromTo . bounds

arbitrarySubset :: IntSet -> Gen IntSet
arbitrarySubset = fmap IntSet.fromAscList . sublistOf . IntSet.toAscList

-- ------------------------------------------------------------------------

case_graphFromEdgesWith :: Assertion
case_graphFromEdgesWith = do
  let g = graphFromEdgesWith (++) 2 [(0, 1, ["world"]), (0, 1, ["hello"])]
  graphToEdges g @?= [(0, 1, ["hello", "world"])]

case_graphFromUnorderedEdgesWith :: Assertion
case_graphFromUnorderedEdgesWith = do
  let g = graphFromUnorderedEdgesWith (++) 2 [(0, 1, ["world"]), (1, 0, ["hello"])]
  graphToUnorderedEdges g @?= [(0, 1, ["hello", "world"])]

prop_graphToEdges :: Property
prop_graphToEdges =
  forAll arbitrary $ \(NonNegative n) -> do
    forAll (arbitraryDiGraph n) $ \g ->
      g === graphFromEdges n (graphToEdges g)

prop_converseGraph_involution :: Property
prop_converseGraph_involution =
  forAll arbitrary $ \(NonNegative n) -> do
    forAll (arbitraryDiGraph n) $ \g ->
      g === converseGraph (converseGraph g)

prop_converseGraph_unordered :: Property
prop_converseGraph_unordered =
  forAll arbitrary $ \(NonNegative n) -> do
    forAll (arbitraryGraph n) $ \g ->
      g === converseGraph g

prop_graphToUnorderedEdges :: Property
prop_graphToUnorderedEdges =
  forAll arbitrary $ \(NonNegative n) -> do
    forAll (arbitraryGraph n) $ \g ->
      g === graphFromUnorderedEdges n (graphToUnorderedEdges g)

prop_independent_set_and_clique :: Property
prop_independent_set_and_clique =
  forAll arbitrary $ \(NonNegative n) -> do
    forAll (arbitrarySimpleGraph n) $ \g ->
      forAll (arbitrarySubset (vertexes g)) $ \s -> do
        counterexample (show (graphToUnorderedEdges g)) $
          s `isIndependentSetOf` g === s `isCliqueOf` complementSimpleGraph g

-- ------------------------------------------------------------------------
-- Test harness

graphTestGroup :: TestTree
graphTestGroup = $(testGroupGenerator)
