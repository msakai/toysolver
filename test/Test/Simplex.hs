{-# LANGUAGE TemplateHaskell #-}
module Test.Simplex (simplexTestGroup) where

import Control.Monad
import Control.Monad.State
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List
import Data.Ratio
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH
import Text.Printf

import qualified ToySolver.Data.LA as LA
import ToySolver.Data.LA ((.<=.))
import ToySolver.Arith.Simplex
import qualified ToySolver.Arith.LPSolver as LP

example_3_2 :: Tableau Rational
example_3_2 = IntMap.fromList
  [ (4, (IntMap.fromList [(1,2), (2,1), (3,1)], 2))
  , (5, (IntMap.fromList [(1,1), (2,2), (3,3)], 5))
  , (6, (IntMap.fromList [(1,2), (2,2), (3,1)], 6))
  , (objRowIndex, (IntMap.fromList [(1,-3), (2,-2), (3,-3)], 0))
  ]

case_example_3_2_simplex :: Assertion
case_example_3_2_simplex = do
  assertBool "simplex failed" ret
  assertBool "invalid tableau" (isValidTableau result)
  assertBool "infeasible tableau" (isFeasible result)
  assertBool "unoptimal tableau" (isOptimal OptMax result)
  currentObjValue result @?= 27/5
  where
    ret :: Bool
    result :: Tableau Rational
    (ret,result) = simplex OptMax example_3_2

case_example_3_2_primalDualSimplex :: Assertion
case_example_3_2_primalDualSimplex = do
  assertBool "simplex failed" ret
  assertBool "invalid tableau" (isValidTableau result)
  assertBool "infeasible tableau" (isFeasible result)
  assertBool "unoptimal tableau" (isOptimal OptMax result)
  currentObjValue result @?= 27/5
  where
    ret :: Bool
    result :: Tableau Rational
    (ret,result) = primalDualSimplex OptMax example_3_2

-- from http://www.math.cuhk.edu.hk/~wei/lpch5.pdf
example_5_3_phase1 :: Tableau Rational
example_5_3_phase1 = IntMap.fromList
  [ (6, (IntMap.fromList [(2,-1), (3,-1), (5,1)], 1))
  , (7, (IntMap.fromList [(3,1), (4,-1), (5,1)], 0))
  ]

case_example_5_3_phase1 :: Assertion
case_example_5_3_phase1 = do
  let (ret,result) = phaseI example_5_3_phase1 (IntSet.fromList [6,7])
  assertBool "phase1 failed" ret
  assertBool "invalid tableau" (isValidTableau result)
  assertBool "infeasible tableau" (isFeasible result)    

-- 退化して巡回の起こるKuhnの7変数3制約の例
kuhn_7_3 :: Tableau Rational
kuhn_7_3 = IntMap.fromList
  [ (1, (IntMap.fromList [(4,-2), (5,-9), (6,1), (7,9)],       0))
  , (2, (IntMap.fromList [(4,1/3), (5,1), (6,-1/3), (7,-2)],   0))
  , (3, (IntMap.fromList [(4,2), (5,3), (6,-1), (7,-12)],      2))
  , (objRowIndex, (IntMap.fromList [(4,2), (5,3), (6,-1), (7,-12)], 0))
  ]

case_kuhn_7_3 :: Assertion
case_kuhn_7_3 = do
  assertBool "simplex failed" ret
  assertBool "invalid tableau" (isValidTableau result)
  currentObjValue result @?= -2
  where
    ret :: Bool
    result :: Tableau Rational
    (ret,result) = simplex OptMin kuhn_7_3

-- case_pd_kuhn_7_3 :: Assertion
-- case_pd_kuhn_7_3 = do
--   assertBool "simplex failed" ret
--   assertBool "invalid tableau" (isValidTableau result)
--   currentObjValue result @?= -2
--   where
--     ret :: Bool
--     result :: Tableau Rational
--     (ret,result) = primalDualSimplex OptMin kuhn_7_3

-- from http://www.math.cuhk.edu.hk/~wei/lpch5.pdf
example_5_7 :: Tableau Rational
example_5_7 = IntMap.fromList
  [ (4, (IntMap.fromList [(1,-1), (2,-2), (3,-3)], -5))
  , (5, (IntMap.fromList [(1,-2), (2,-2), (3,-1)], -6))
  , (objRowIndex, (IntMap.fromList [(1,3),(2,4),(3,5)], 0))
  ]

case_example_5_7 :: Assertion
case_example_5_7 = do
  assertBool "dual simplex failed" ret
  assertBool "invalid tableau" (isValidTableau result)
  currentObjValue result @?= -11
  where
    ret :: Bool
    result :: Tableau Rational
    (ret,result) = dualSimplex OptMax example_5_7

case_pd_example_5_7 :: Assertion
case_pd_example_5_7 = do
  assertBool "dual simplex failed" ret
  assertBool "invalid tableau" (isValidTableau result)
  currentObjValue result @?= -11
  where
    ret :: Bool
    result :: Tableau Rational
    (ret,result) = primalDualSimplex OptMax example_5_7

------------------------------------------------------------------------

case_lp_example_5_7_twoPhaseSimplex :: Assertion
case_lp_example_5_7_twoPhaseSimplex = do  
  ret @?= LP.Optimum
  oval @?= -11
  assertBool "invalid tableau" (isValidTableau tbl)
  assertBool "infeasible tableau" (isFeasible tbl)
  assertBool "non-optimal tableau" (isOptimal OptMax tbl)
  where
    oval :: Rational
    ((ret,tbl,oval),result) = flip runState (LP.emptySolver IntSet.empty) $ do
      _ <- LP.newVar
      x1 <- LP.newVar 
      x2 <- LP.newVar
      x3 <- LP.newVar
      LP.addConstraint (LA.fromTerms [(-1,x1),(-2,x2),(-3,x3)] .<=. LA.constant (-5))
      LP.addConstraint (LA.fromTerms [(-2,x1),(-2,x2),(-1,x3)] .<=. LA.constant (-6))
      let obj = LA.fromTerms [(-3,x1), (-4,x2),(-5,x3)]
      ret <- LP.twoPhaseSimplex OptMax obj
      tbl <- LP.getTableau
      m <- LP.getModel (IntSet.fromList [x1,x2,x3])
      let oval = LA.eval m obj
      return (ret,tbl,oval)

case_lp_example_5_7_primalDualSimplex :: Assertion
case_lp_example_5_7_primalDualSimplex = do  
  ret @?= LP.Optimum
  oval @?= -11
  assertBool "invalid tableau" (isValidTableau tbl)
  assertBool "infeasible tableau" (isFeasible tbl)
  assertBool "non-optimal tableau" (isOptimal OptMax tbl)
  where
    oval :: Rational
    ((ret,tbl,oval),result) = flip runState (LP.emptySolver IntSet.empty) $ do
      _ <- LP.newVar
      x1 <- LP.newVar 
      x2 <- LP.newVar
      x3 <- LP.newVar
      LP.addConstraint (LA.fromTerms [(-1,x1),(-2,x2),(-3,x3)] .<=. LA.constant (-5))
      LP.addConstraint (LA.fromTerms [(-2,x1),(-2,x2),(-1,x3)] .<=. LA.constant (-6))
      let obj = LA.fromTerms [(-3,x1), (-4,x2),(-5,x3)]
      ret <- LP.primalDualSimplex OptMax obj
      tbl <- LP.getTableau
      m <- LP.getModel (IntSet.fromList [x1,x2,x3])
      let oval = LA.eval m obj
      return (ret,tbl,oval)

------------------------------------------------------------------------
-- Test harness

simplexTestGroup :: TestTree
simplexTestGroup = $(testGroupGenerator)
