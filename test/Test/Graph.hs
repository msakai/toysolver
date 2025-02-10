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

case_graphFromUnorderedEdgesWith :: Assertion
case_graphFromUnorderedEdgesWith = do
  let g = graphFromUnorderedEdgesWith (++) 2 [(0, 1, ["world"]), (1, 0, ["hello"])]
  graphToUnorderedEdges g @?= [(0, 1, ["hello", "world"])]

prop_graphToUnorderedEdges :: Property
prop_graphToUnorderedEdges =
  forAll arbitrary $ \(NonNegative n) -> do
    forAll (arbitraryGraph n) $ \g ->
      g === graphFromUnorderedEdges n (graphToUnorderedEdges g)

prop_indepndent_set_and_clique :: Property
prop_indepndent_set_and_clique =
  forAll arbitrary $ \(NonNegative n) -> do
    forAll (arbitrarySimpleGraph n) $ \g ->
      forAll (arbitrarySubset (vertexes g)) $ \s -> do
        counterexample (show (graphToUnorderedEdges g)) $
          s `isIndependentSetOf` g === s `isCliqueOf` complementSimpleGraph g

-- ------------------------------------------------------------------------
-- Test harness

graphTestGroup :: TestTree
graphTestGroup = $(testGroupGenerator)
