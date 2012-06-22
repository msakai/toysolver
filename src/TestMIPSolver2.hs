{-# LANGUAGE TemplateHaskell #-}
module Main (main) where

import Control.Monad
import Data.List
import Data.Ratio
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Test.HUnit hiding (Test)
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Text.Printf

import Data.Linear
import Simplex2
import MIPSolver2
import qualified Data.LA as LA

------------------------------------------------------------------------

example1 :: (OptDir, LA.Expr Rational, [Atom Rational], IS.IntSet)
example1 = (optdir, obj, cs, ivs)
  where
    optdir = OptMax
    x1 = LA.var 1
    x2 = LA.var 2
    x3 = LA.var 3
    x4 = LA.var 4
    obj = x1 .+. 2 .*. x2 .+. 3 .*. x3 .+. x4
    cs =
      [ LA.Atom ((-1) .*. x1 .+. x2 .+. x3 .+. 10.*.x4) Le (LA.constant 20)
      , LA.Atom (x1 .-. 3 .*. x2 .+. x3) Le (LA.constant 30)
      , LA.Atom (x2 .-. 3.5 .*. x4) Eql (LA.constant 0)
      , LA.Atom (LA.constant 0) Le x1
      , LA.Atom x1 Le (LA.constant 40)
      , LA.Atom (LA.constant 0) Le x2
      , LA.Atom (LA.constant 0) Le x3
      , LA.Atom (LA.constant 2) Le x4
      , LA.Atom x4 Le (LA.constant 3)
      ]
    ivs = IS.singleton 4

case_test1 = do
  let (optdir, obj, cs, ivs) = example1
  lp <- Simplex2.newSolver
  replicateM 5 (Simplex2.newVar lp)
  setOptDir lp optdir
  setObj lp obj
  mapM_ (Simplex2.assertAtom lp) cs
  mip <- MIPSolver2.newSolver lp ivs
  ret <- MIPSolver2.optimize mip (\_ _ -> return ())
  
  ret @?= Simplex2.Optimum

  m <- MIPSolver2.model mip
  forM_ [(1,40 % 1),(2,21 % 2),(3,39 % 2),(4,3 % 1)] $ \(var, val) ->
    m IM.! var @?= val

  v <- MIPSolver2.getObjValue mip
  v @?= (245 % 2)

case_test1' = do
  let (optdir, obj, cs, ivs) = example1
  lp <- Simplex2.newSolver
  replicateM 5 (Simplex2.newVar lp)
  setOptDir lp (f optdir)
  setObj lp (lnegate obj)
  mapM_ (Simplex2.assertAtom lp) cs
  mip <- MIPSolver2.newSolver lp ivs
  ret <- MIPSolver2.optimize mip (\_ _ -> return ())
  
  ret @?= Simplex2.Optimum

  m <- MIPSolver2.model mip
  forM_ [(1,40 % 1),(2,21 % 2),(3,39 % 2),(4,3 % 1)] $ \(var, val) ->
    m IM.! var @?= val

  v <- MIPSolver2.getObjValue mip
  v @?= (- 245 % 2)

  where
    f OptMin = OptMax
    f OptMax = OptMin

-- 『数理計画法の基礎』(坂和 正敏) p.109 例 3.8
example2 = (optdir, obj, cs, ivs)
  where
    optdir = OptMin
    [x1,x2,x3] = map LA.var [1..3]
    obj = (-1) .*. x1 .-. 3 .*. x2 .-. 5 .*. x3
    cs =
      [ LA.Atom (3 .*. x1 .+. 4 .*. x2) Le (LA.constant 10)
      , LA.Atom (2 .*. x1 .+. x2 .+. x3) Le (LA.constant 7)
      , LA.Atom (3.*.x1 .+. x2 .+. 4 .*. x3) Eql (LA.constant 12)
      , LA.Atom (LA.constant 0) Le x1
      , LA.Atom (LA.constant 0) Le x2
      , LA.Atom (LA.constant 0) Le x3
      ]
    ivs = IS.fromList [1,2]

case_test2 = do
  let (optdir, obj, cs, ivs) = example2
  lp <- Simplex2.newSolver
  replicateM 4 (Simplex2.newVar lp)
  setOptDir lp optdir
  setObj lp obj
  mapM_ (Simplex2.assertAtom lp) cs
  mip <- MIPSolver2.newSolver lp ivs
  ret <- MIPSolver2.optimize mip (\_ _ -> return ())
  
  ret @?= Simplex2.Optimum

  m <- MIPSolver2.model mip
  forM_ [(1,0 % 1),(2,2 % 1),(3,5 % 2)] $ \(var, val) ->
    m IM.! var @?= val

  v <- MIPSolver2.getObjValue mip
  v @?= (- 37 % 2)

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
