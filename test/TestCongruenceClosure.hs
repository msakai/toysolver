{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module Main (main) where

import Control.Monad
import Data.Array
import Data.Graph
import qualified Data.Tree as Tree
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

  mergeFlatTerm solver (FTConst a, c)
  ret <- areCongruentFlatTerm solver (FTApp a b) (FTApp c d)
  ret @?= False
  
  mergeFlatTerm solver (FTConst b, d)
  ret <- areCongruentFlatTerm solver (FTApp a b) (FTApp c d)
  ret @?= True

case_Example_11 :: IO ()
case_Example_11 = do
  solver <- newSolver
  replicateM_ 15 $ newVar solver
  let xs = [(1,8),(7,2),(3,13),(7,1),(6,7),(6,7),(9,5),(9,3),(14,11),(10,4),(12,9),(4,11),(10,7)]
  forM_ xs $ \(a,b) -> mergeFlatTerm solver (FTConst a, b)
  m <- explainFlatTerm solver 1 4
  fmap Set.fromList m @?= Just (Set.fromList [Left (7,1),Left (10,4),Left (10,7)])

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
  mergeFlatTerm solver (FTApp g h, d)
  mergeFlatTerm solver (FTConst c, d)
  mergeFlatTerm solver (FTApp g d, a)
  mergeFlatTerm solver (FTConst e, c)
  mergeFlatTerm solver (FTConst e, b)
  mergeFlatTerm solver (FTConst b, h)
  m <- explainFlatTerm solver a b
  fmap Set.fromList m @?= Just (Set.fromList [Left (c,d),Left (e,c),Left (e,b),Left (b,h),Right (Eqn1 g h d,Eqn1 g d a)])
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
    forM_ edges $ \(s,t) -> mergeFlatTerm solver (FTConst s, t)
  forM_ [0..(nv-1)] $ \c ->
    forM_ [0..(nv-1)] $ \d -> do
      b <- QM.run $ areCongruentFlatTerm solver (FTConst c) (FTConst d)
      QM.assert $ b == (repr ! c == repr ! d)

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
