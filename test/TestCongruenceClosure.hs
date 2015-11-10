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

import ToySolver.EUF.CongruenceClosure

------------------------------------------------------------------------
-- Test cases

case_Example_1 :: IO ()
case_Example_1 = do
  solver <- newSolver
  a <- newFSym solver
  b <- newFSym solver
  c <- newFSym solver
  d <- newFSym solver

  merge solver (TApp a []) (TApp c [])
  ret <- areCongruent solver (TApp a [TApp b []]) (TApp c [TApp d []])
  ret @?= False
  
  merge solver (TApp b []) (TApp d [])
  ret <- areCongruent solver (TApp a [TApp b []]) (TApp c [TApp d []])
  ret @?= True

case_Example_1_FlatTerm :: IO ()
case_Example_1_FlatTerm = do
  solver <- newSolver
  a <- newFSym solver
  b <- newFSym solver
  c <- newFSym solver
  d <- newFSym solver

  mergeFlatTerm solver (FTConst a) c
  ret <- areCongruentFlatTerm solver (FTApp a b) (FTApp c d)
  ret @?= False
  
  mergeFlatTerm solver (FTConst b) d
  ret <- areCongruentFlatTerm solver (FTApp a b) (FTApp c d)
  ret @?= True
  
case_Example_2 :: IO ()
case_Example_2 = do
  solver <- newSolver
  a <- newConst solver
  b <- newConst solver
  c <- newConst solver
  d <- newConst solver
  f <- liftM (\c x -> TApp c [x]) $ newFSym solver
  g <- liftM (\c x -> TApp c [x]) $ newFSym solver
  h <- liftM (\c x y -> TApp c [x,y]) $ newFSym solver  
  
  merge solver (f b) c
  merge solver (f c) a
  merge solver (g a) (h a a)
  ret <- areCongruent solver (g b) (h c b)
  ret @?= False
  
  merge solver b c
  ret <- areCongruent solver (g b) (h c b)
  ret @?= True

case_NO2007_Example_11 :: IO ()
case_NO2007_Example_11 = do
  solver <- newSolver
  replicateM_ 15 $ newFSym solver
  let xs = [(1,8),(7,2),(3,13),(7,1),(6,7),(6,7),(9,5),(9,3),(14,11),(10,4),(12,9),(4,11),(10,7)]
  forM_ (zip [0..] xs) $ \(i,(a,b)) -> mergeFlatTerm' solver (FTConst a) b (Just i)
  m <- explainConst solver 1 4
  fmap (Set.fromList . map (xs!!) . IntSet.toList) m @?= Just (Set.fromList [(7,1), (10,4), (10,7)])

-- f(g,h)=d, c=d, f(g,d)=a, e=c, e=b, b=h
case_NO2007_Example_16 :: IO ()
case_NO2007_Example_16 = do
  solver <- newSolver
  a <- newFSym solver
  b <- newFSym solver  
  c <- newFSym solver
  d <- newFSym solver
  e <- newFSym solver
  g <- newFSym solver
  h <- newFSym solver
  mergeFlatTerm' solver (FTApp g h) d (Just 0)
  mergeFlatTerm' solver (FTConst c) d (Just 1)
  mergeFlatTerm' solver (FTApp g d) a (Just 2)
  mergeFlatTerm' solver (FTConst e) c (Just 3)
  mergeFlatTerm' solver (FTConst e) b (Just 4)
  mergeFlatTerm' solver (FTConst b) h (Just 5)
  m <- explainConst solver a b
  m @?= Just (IntSet.fromList [1,3,4,5,0,2])
  -- d = c = e = b = h
  -- a = f(g,d) = f(g,h) = d = c = e = b

case_backtracking_1 :: IO ()
case_backtracking_1 = do
  solver <- newSolver
  a1 <- newFSym solver
  a2 <- newFSym solver
  b1 <- newFSym solver
  b2 <- newFSym solver

  mergeFlatTerm solver (FTConst a1) b1

  pushBacktrackPoint solver
  mergeFlatTerm solver (FTConst a2) b2
  ret <- areCongruentFlatTerm solver (FTApp a1 a2) (FTApp b1 b2)
  ret @?= True
  popBacktrackPoint solver

  ret <- areCongruentFlatTerm solver (FTConst a2) (FTConst b2)
  ret @?= False
  ret <- areCongruentFlatTerm solver (FTApp a1 a2) (FTApp b1 b2)
  ret @?= False

  pushBacktrackPoint solver
  ret <- areCongruentFlatTerm solver (FTConst a2) (FTConst b2)
  ret @?= False
  ret <- areCongruentFlatTerm solver (FTApp a1 a2) (FTApp b1 b2)
  ret @?= False  
  popBacktrackPoint solver

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
    replicateM_ nv $ newFSym solver
    forM_ edges $ \(s,t) -> mergeFlatTerm solver (FTConst s) t
  forM_ [0..(nv-1)] $ \c ->
    forM_ [0..(nv-1)] $ \d -> do
      b <- QM.run $ areCongruentFlatTerm solver (FTConst c) (FTConst d)
      QM.assert $ b == (repr ! c == repr ! d)

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
