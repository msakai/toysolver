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
import Test.Tasty.QuickCheck
import Test.Tasty.TH

import ToySolver.Graph.Base


-- ------------------------------------------------------------------------

arbitrarySimpleGraph :: Gen Graph
arbitrarySimpleGraph = do
  sized $ \n -> do
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

prop_indepndent_set_and_clique :: Property
prop_indepndent_set_and_clique =
  forAll arbitrarySimpleGraph $ \g ->
    forAll (arbitrarySubset (vertexes g)) $ \s -> do
      counterexample (show (graphToUnorderedEdges g)) $
        s `isIndependentSetOf` g === s `isCliqueOf` complementSimpleGraph g

-- ------------------------------------------------------------------------
-- Test harness

graphTestGroup :: TestTree
graphTestGroup = $(testGroupGenerator)
