{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Test.GraphShortestPath (graphShortestPathTestGroup) where

import Control.Monad
import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.TH
import ToySolver.Graph.ShortestPath
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap

-- ------------------------------------------------------------------------

type Vertex = Int
type Cost = Rational
type Label = Char
    
genGraph :: Gen Cost -> Gen (HashMap Vertex [OutEdge Vertex Cost Label])
genGraph genCost = do
  n <- choose (1, 20) -- inclusive
  liftM HashMap.fromList $ forM [1..n] $ \i -> do
    m <- choose (0, min (n+1) 20)
    ys <- replicateM m $ do
      j <- choose (1, n)
      c <- genCost
      l <- elements ['A'..'Z']
      return (j,c,l)
    return (i, ys)

genGraphNonNegative :: Gen (HashMap Vertex [OutEdge Vertex Cost Label])
genGraphNonNegative = genGraph (liftM getNonNegative arbitrary)

isValidEdge :: HashMap Vertex [OutEdge Vertex Cost Label] -> Edge Vertex Cost Label -> Bool
isValidEdge g (v,u,c,l) =
  case HashMap.lookup  v g of
    Nothing -> False
    Just outs -> (u,c,l) `elem` outs

isValidPath :: HashMap Vertex [OutEdge Vertex Cost Label] -> Path Vertex Cost Label -> Bool
isValidPath g = f
  where
    f (Empty v) = v `HashMap.member` g
    f (Singleton e) = isValidEdge g e
    f (Append p1 p2 c) = f p1 && f p2 && pathTo p1 == pathFrom p2 && pathCost p1 + pathCost p2 == c

-- ------------------------------------------------------------------------

prop_bellmanFord_valid_path :: Property
prop_bellmanFord_valid_path =
  forAll (genGraph arbitrary) $ \g ->
    forAll (sublistOf (HashMap.keys g)) $ \ss ->
      case bellmanFord g ss of
        Left cyclePath ->
          isValidPath g cyclePath &&
          pathFrom cyclePath == pathTo cyclePath &&
          pathCost cyclePath < 0
        Right m -> and
          [ isValidPath g path &&
            pathTo path == u &&
            pathFrom path `elem` ss
          | (u, path) <- HashMap.toList $ buildPaths m
          ]

prop_dijkstra_valid_path :: Property
prop_dijkstra_valid_path =
  forAll (genGraphNonNegative) $ \g ->
    forAll (sublistOf (HashMap.keys g)) $ \ss ->
      and
      [ isValidPath g path &&
        pathTo path == u &&
        pathFrom path `elem` ss
      | (u, path) <- HashMap.toList $ buildPaths $ dijkstra g ss
      ]

prop_floydWarshall_valid_path :: Property
prop_floydWarshall_valid_path =
  forAll (genGraphNonNegative) $ \g ->
      and
      [ isValidPath g path &&
        pathFrom path == u &&
        pathTo path == v
      | ((u,v), path) <- HashMap.toList (floydWarshall g)
      ]

prop_dijkstra_equals_bellmanFord :: Property
prop_dijkstra_equals_bellmanFord =
  forAll (genGraphNonNegative) $ \g ->
    let vs = HashMap.keys g
    in forAll (elements vs) $ \v ->
       forAll (elements vs) $ \u ->
         ((Right . fmap pathCost . HashMap.lookup u . buildPaths) $ dijkstra g [v])
         ==
         (fmap (fmap pathCost . HashMap.lookup u . buildPaths) $ bellmanFord g [v])

prop_floydWarshall_equals_dijkstra :: Property
prop_floydWarshall_equals_dijkstra =
  forAll (genGraphNonNegative) $ \g ->
    let vs = HashMap.keys g
        m  = floydWarshall g        
    in forAll (elements vs) $ \v ->
       forAll (elements vs) $ \u ->
         fmap pathCost (HashMap.lookup (v,u) m)
         ==
         fmap pathCost (HashMap.lookup u $ buildPaths $ dijkstra g [v])

prop_floydWarshall_equals_bellmanFord :: Property
prop_floydWarshall_equals_bellmanFord =
  forAll (genGraph arbitrary) $ \g ->
    let vs = HashMap.keys g
        ret1 = floydWarshall g
    in counterexample (show ret1) $ conjoin $
         [ counterexample (show v) $ counterexample (show ret2) $
             case ret2 of
               Left cyclePath ->
                 conjoin
                 [ counterexample (show u) (pathCost (ret1 HashMap.! (u,u)) < 0)
                 | u <- pathVertexes cyclePath
                 ]
               Right m2 ->
                 HashMap.fromList [(u, pathCost path) | ((v',u), path) <- HashMap.toList ret1, v==v']
                 ===
                 fmap fst m2
         | v <- vs, let ret2 = bellmanFord g [v]
         ]

-- ------------------------------------------------------------------------
-- Test harness

graphShortestPathTestGroup :: TestTree
graphShortestPathTestGroup = $(testGroupGenerator)
