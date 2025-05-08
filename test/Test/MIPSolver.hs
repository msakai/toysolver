{-# LANGUAGE TemplateHaskell #-}
module Test.MIPSolver (mipSolverTestGroup) where

import Control.Monad
import Data.Ratio
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.VectorSpace
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH
import Text.Printf

import qualified ToySolver.Data.LA as LA
import qualified ToySolver.Arith.Simplex as Simplex
import ToySolver.Arith.Simplex
import qualified ToySolver.Arith.MIP as MIPSolver

------------------------------------------------------------------------

example1 :: (OptDir, LA.Expr Rational, [Atom Rational], IS.IntSet)
example1 = (optdir, obj, cs, ivs)
  where
    optdir = OptMax
    x1 = LA.var 1
    x2 = LA.var 2
    x3 = LA.var 3
    x4 = LA.var 4
    obj = x1 ^+^ 2 *^ x2 ^+^ 3 *^ x3 ^+^ x4
    cs =
      [ (-1) *^ x1 ^+^ x2 ^+^ x3 ^+^ 10*^x4 .<=. LA.constant 20
      , x1 ^-^ 3 *^ x2 ^+^ x3 .<=. LA.constant 30
      , x2 ^-^ 3.5 *^ x4 .==. LA.constant 0
      , LA.constant 0 .<=. x1
      , x1 .<=. LA.constant 40
      , LA.constant 0 .<=. x2
      , LA.constant 0 .<=. x3
      , LA.constant 2 .<=. x4
      , x4 .<=. LA.constant 3
      ]
    ivs = IS.singleton 4

case_test1 = do
  let (optdir, obj, cs, ivs) = example1
  lp <- Simplex.newSolver
  replicateM 5 (Simplex.newVar lp)
  setOptDir lp optdir
  setObj lp obj
  mapM_ (Simplex.assertAtom lp) cs
  mip <- MIPSolver.newSolver lp ivs
  ret <- MIPSolver.optimize mip

  ret @?= Simplex.Optimum

  Just m <- MIPSolver.getBestModel mip
  forM_ [(1,40),(2,21/2),(3,39/2),(4,3)] $ \(var, val) ->
    m IM.! var @?= val

  Just v <- MIPSolver.getBestValue mip
  v @?= 245/2

case_test1' = do
  let (optdir, obj, cs, ivs) = example1
  lp <- Simplex.newSolver
  replicateM 5 (Simplex.newVar lp)
  setOptDir lp (f optdir)
  setObj lp (negateV obj)
  mapM_ (Simplex.assertAtom lp) cs
  mip <- MIPSolver.newSolver lp ivs
  ret <- MIPSolver.optimize mip

  ret @?= Simplex.Optimum

  Just m <- MIPSolver.getBestModel mip
  forM_ [(1,40),(2,21/2),(3,39/2),(4,3)] $ \(var, val) ->
    m IM.! var @?= val

  Just v <- MIPSolver.getBestValue mip
  v @?= -245/2

  where
    f OptMin = OptMax
    f OptMax = OptMin

-- 『数理計画法の基礎』(坂和 正敏) p.109 例 3.8
example2 = (optdir, obj, cs, ivs)
  where
    optdir = OptMin
    [x1,x2,x3] = map LA.var [1..3]
    obj = (-1) *^ x1 ^-^ 3 *^ x2 ^-^ 5 *^ x3
    cs =
      [ 3 *^ x1 ^+^ 4 *^ x2 .<=. LA.constant 10
      , 2 *^ x1 ^+^ x2 ^+^ x3 .<=. LA.constant 7
      , 3 *^ x1 ^+^ x2 ^+^ 4 *^ x3 .==. LA.constant 12
      , LA.constant 0 .<=. x1
      , LA.constant 0 .<=. x2
      , LA.constant 0 .<=. x3
      ]
    ivs = IS.fromList [1,2]

case_test2 = do
  let (optdir, obj, cs, ivs) = example2
  lp <- Simplex.newSolver
  replicateM 4 (Simplex.newVar lp)
  setOptDir lp optdir
  setObj lp obj
  mapM_ (Simplex.assertAtom lp) cs
  mip <- MIPSolver.newSolver lp ivs
  ret <- MIPSolver.optimize mip

  ret @?= Simplex.Optimum

  Just m <- MIPSolver.getBestModel mip
  forM_ [(1,0),(2,2),(3,5/2)] $ \(var, val) ->
    m IM.! var @?= val

  Just v <- MIPSolver.getBestValue mip
  v @?= -37/2

------------------------------------------------------------------------
-- Test harness

mipSolverTestGroup :: TestTree
mipSolverTestGroup = $(testGroupGenerator)
