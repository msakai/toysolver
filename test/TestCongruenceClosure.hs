{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module Main (main) where

import Control.Monad
import Data.Array
import Data.Graph
import qualified Data.Tree as Tree
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import qualified Data.Set as Set

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import ToySolver.CongruenceClosure

------------------------------------------------------------------------
-- Test cases

case_1 :: IO ()
case_1 = do
  solver <- newSolver
  a <- newVar solver
  b <- newVar solver
  c <- newVar solver
  d <- newVar solver

  merge solver (TApp a []) (TApp c [])
  ret <- areCongruent solver (TApp a [TApp b []]) (TApp c [TApp d []])
  ret @?= False
  
  merge solver (TApp b []) (TApp d [])
  ret <- areCongruent solver (TApp a [TApp b []]) (TApp c [TApp d []])
  ret @?= True

case_1_FlatTerm :: IO ()
case_1_FlatTerm = do
  solver <- newSolver
  a <- newVar solver
  b <- newVar solver
  c <- newVar solver
  d <- newVar solver

  mergeFlatTerm solver (FTConst a) c
  ret <- areCongruentFlatTerm solver (FTApp a b) (FTApp c d)
  ret @?= False
  
  mergeFlatTerm solver (FTConst b) d
  ret <- areCongruentFlatTerm solver (FTApp a b) (FTApp c d)
  ret @?= True

case_Example_11 :: IO ()
case_Example_11 = do
  solver <- newSolver
  replicateM_ 15 $ newVar solver
  let xs = [(1,8),(7,2),(3,13),(7,1),(6,7),(6,7),(9,5),(9,3),(14,11),(10,4),(12,9),(4,11),(10,7)]
  forM_ (zip [0..] xs) $ \(i,(a,b)) -> mergeFlatTerm' solver (FTConst a) b (Just i)
  m <- explainVar solver 1 4
  fmap (Set.fromList . map (xs!!) . IntSet.toList) m @?= Just (Set.fromList [(7,1), (10,4), (10,7)])

-- f(g,h)=d, c=d, f(g,d)=a, e=c, e=b, b=h
case_Example_16 :: IO ()
case_Example_16 = do
  solver <- newSolver
  a <- newVar solver
  b <- newVar solver  
  c <- newVar solver
  d <- newVar solver
  e <- newVar solver
  g <- newVar solver
  h <- newVar solver
  mergeFlatTerm' solver (FTApp g h) d (Just 0)
  mergeFlatTerm' solver (FTConst c) d (Just 1)
  mergeFlatTerm' solver (FTApp g d) a (Just 2)
  mergeFlatTerm' solver (FTConst e) c (Just 3)
  mergeFlatTerm' solver (FTConst e) b (Just 4)
  mergeFlatTerm' solver (FTConst b) h (Just 5)
  m <- explainVar solver a b
  m @?= Just (IntSet.fromList [1,3,4,5,0,2])
  -- d = c = e = b = h
  -- a = f(g,d) = f(g,h) = d = c = e = b

prop_components :: Property
prop_components = QM.monadicIO $ do
  nv <- QM.pick $ choose (1, 10)
  ne <- QM.pick $ choose (1, 100)
  edges <- QM.pick $ replicateM ne $ do
    s <- choose (0,nv-1)
    t <- choose (0,nv-1)
    return (s,t)
  let g = buildG (0,nv-1) edges
      comps = map Tree.flatten $ components g
      repr = array (0,nv-1) [(c, Tree.rootLabel comp) | comp <- components g, c <- Tree.flatten comp]

  solver <- QM.run $ newSolver
  QM.run $ do
    replicateM_ nv $ newVar solver
    forM_ edges $ \(s,t) -> mergeFlatTerm solver (FTConst s) t
  forM_ [0..(nv-1)] $ \c ->
    forM_ [0..(nv-1)] $ \d -> do
      b <- QM.run $ areCongruentFlatTerm solver (FTConst c) (FTConst d)
      QM.assert $ b == (repr ! c == repr ! d)

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
