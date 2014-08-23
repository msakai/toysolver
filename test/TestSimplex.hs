{-# LANGUAGE TemplateHaskell #-}
module Main (main) where

import Control.Monad
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List
import Data.Ratio
import Test.HUnit hiding (Test)
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Text.Printf

import ToySolver.Simplex

-- from http://www.math.cuhk.edu.hk/~wei/lpch5.pdf
exampe_5_3_phase1 :: Tableau Rational
exampe_5_3_phase1 = IntMap.fromList
  [ (6, (IntMap.fromList [(2,-1), (3,-1), (5,1), (6,1)], 1))
  , (7, (IntMap.fromList [(3,1), (4,-1), (5,1), (7,1)], 0))
  ]

case_exampe_5_3_phase1 :: IO ()
case_exampe_5_3_phase1 = do
  let (ret,result) = phaseI exampe_5_3_phase1 (IntSet.fromList [6,7])
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

case_kuhn_7_3 :: IO ()
case_kuhn_7_3 = do
  assertBool "simplex failed" ret
  assertBool "invalid tableau" (isValidTableau result)
  currentObjValue result @?= -2
  where
    ret :: Bool
    result :: Tableau Rational
    (ret,result) = simplex OptMin kuhn_7_3

-- from http://www.math.cuhk.edu.hk/~wei/lpch5.pdf
example_5_7 :: Tableau Rational
example_5_7 = IntMap.fromList
  [ (4, (IntMap.fromList [(1,-1), (2,-2), (3,-3)], -5))
  , (5, (IntMap.fromList [(1,-2), (2,-2), (3,-1)], -6))
  , (objRowIndex, (IntMap.fromList [(1,3),(2,4),(3,5)], 0))
  ]

case_example_5_7 :: IO ()
case_example_5_7 = do
  assertBool "dual simplex failed" ret
  assertBool "invalid tableau" (isValidTableau result)
  currentObjValue result @?= -11
  where
    ret :: Bool
    result :: Tableau Rational
    (ret,result) = dualSimplex OptMax example_5_7

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
