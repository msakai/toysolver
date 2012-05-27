{-# LANGUAGE TemplateHaskell #-}
module Main (main) where

import Control.Monad
import Data.List
import Test.HUnit hiding (Test)
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Text.Printf

import Simplex2
import qualified LA as LA
-- import qualified Formula as F
-- import Linear

case_test1 :: IO ()
case_test1 = do
  solver <- newSolver
  x <- newVar solver
  y <- newVar solver
  z <- newVar solver
  assertAtom solver (LA.fromTerms [(7,x), (12,y), (31,z)] .==. LA.constExpr 17)
  assertAtom solver (LA.fromTerms [(3,x), (5,y), (14,z)]  .==. LA.constExpr 7)
  assertAtom solver (LA.varExpr x .>=. LA.constExpr 1)
  assertAtom solver (LA.varExpr x .<=. LA.constExpr 40)
  assertAtom solver (LA.varExpr y .>=. LA.constExpr (-50))
  assertAtom solver (LA.varExpr y .<=. LA.constExpr 50)

  ret <- check solver
  ret @?= True

  vx <- getValue solver x
  vy <- getValue solver y
  vz <- getValue solver z
  7*vx + 12*vy + 31*vz @?= 17
  3*vx + 5*vy + 14*vz @?= 7
  assertBool (printf "vx should be >=1 but %s"   (show vx)) $ vx >= 1
  assertBool (printf "vx should be <=40 but %s"  (show vx)) $ vx <= 40
  assertBool (printf "vx should be >=-50 but %s" (show vy)) $ vy >= -50
  assertBool (printf "vx should be <=50 but %s"  (show vy)) $ vy <= 50

case_test2 :: IO ()
case_test2 = do
  solver <- newSolver
  x <- newVar solver
  y <- newVar solver
  assertAtom solver (LA.fromTerms [(11,x), (13,y)] .>=. LA.constExpr 27)
  assertAtom solver (LA.fromTerms [(11,x), (13,y)] .<=. LA.constExpr 45)
  assertAtom solver (LA.fromTerms [(7,x), (-9,y)] .>=. LA.constExpr (-10))
  assertAtom solver (LA.fromTerms [(7,x), (-9,y)] .<=. LA.constExpr 4)

  ret <- check solver
  ret @?= True

  vx <- getValue solver x
  vy <- getValue solver y
  let v1 = 11*vx + 13*vy
      v2 = 7*vx - 9*vy
  assertBool (printf "11*vx + 13*vy should be >=27 but %s" (show v1)) $ 27 <= v1
  assertBool (printf "11*vx + 13*vy should be <=45 but %s" (show v1)) $ v1 <= 45
  assertBool (printf "7*vx - 9*vy should be >=-10 but %s" (show v2)) $ -10 <= v2
  assertBool (printf "7*vx - 9*vy should be >=-10 but %s" (show v2)) $ v2 <= 4


{-
Minimize
 obj: - x1 - 2 x2 - 3 x3 - x4
Subject To
 c1: - x1 + x2 + x3 + 10 x4 <= 20
 c2: x1 - 3 x2 + x3 <= 30
 c3: x2 - 3.5 x4 = 0
Bounds
 0 <= x1 <= 40
 2 <= x4 <= 3
End
-}
case_test3 :: IO ()
case_test3 = do
  solver <- newSolver

  _ <- newVar solver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver

  setObj solver (LA.fromTerms [(-1,x1), (-2,x2), (-3,x3), (-1,x4)])

  assertAtom solver (LA.fromTerms [(-1,x1), (1,x2), (1,x3), (10,x4)] .<=. LA.constExpr 20)
  assertAtom solver (LA.fromTerms [(1,x1), (-3,x2), (1,x3)] .<=. LA.constExpr 30)
  assertAtom solver (LA.fromTerms [(1,x2), (-3.5,x4)] .==. LA.constExpr 0)

  assertAtom solver (LA.fromTerms [(1,x1)] .>=. LA.constExpr 0)
  assertAtom solver (LA.fromTerms [(1,x1)] .<=. LA.constExpr 40)
  assertAtom solver (LA.fromTerms [(1,x2)] .>=. LA.constExpr 0)
  assertAtom solver (LA.fromTerms [(1,x3)] .>=. LA.constExpr 0)
  assertAtom solver (LA.fromTerms [(1,x4)] .>=. LA.constExpr 2)
  assertAtom solver (LA.fromTerms [(1,x4)] .<=. LA.constExpr 3)

  ret1 <- check solver
  ret1 @?= True

  ret2 <- optimize solver defaultOptions
  ret2 @?= Optimum

{-
http://www.math.cuhk.edu.hk/~wei/lpch5.pdf
example 5.7

minimize 3 x1 + 4 x2 + 5 x3
subject to 
1 x1 + 2 x2 + 3 x3 >= 5
2 x1 + 2 x2 + 1 x3 >= 6

optimal value is 11
-}
case_test6 :: IO ()
case_test6 = do
  solver <- newSolver

  _  <- newVar solver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver

  assertLower solver x1 0
  assertLower solver x2 0
  assertLower solver x3 0
  assertAtom solver (LA.fromTerms [(1,x1),(2,x2),(3,x3)] .>=. LA.constExpr 5)
  assertAtom solver (LA.fromTerms [(2,x1),(2,x2),(1,x3)] .>=. LA.constExpr 6)

  setObj solver (LA.fromTerms [(3,x1),(4,x2),(5,x3)])
  setOptDir solver OptMin
  b <- isOptimal solver
  assertBool "should be optimal" $ b

  ret <- dualSimplex solver defaultOptions
  ret @?= Optimum

  val <- getObjValue solver
  val @?= 11

{-
http://www.math.cuhk.edu.hk/~wei/lpch5.pdf
example 5.7

maximize -3 x1 -4 x2 -5 x3
subject to 
-1 x1 -2 x2 -3 x3 <= -5
-2 x1 -2 x2 -1 x3 <= -6

optimal value should be -11
-}
case_test7 :: IO ()
case_test7 = do
  solver <- newSolver

  _  <- newVar solver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver

  assertLower solver x1 0
  assertLower solver x2 0
  assertLower solver x3 0
  assertAtom solver (LA.fromTerms [(-1,x1),(-2,x2),(-3,x3)] .<=. LA.constExpr (-5))
  assertAtom solver (LA.fromTerms [(-2,x1),(-2,x2),(-1,x3)] .<=. LA.constExpr (-6))

  setObj solver (LA.fromTerms [(-3,x1),(-4,x2),(-5,x3)])
  setOptDir solver OptMax
  b <- isOptimal solver
  assertBool "should be optimal" $ b

  ret <- dualSimplex solver defaultOptions
  ret @?= Optimum

  val <- getObjValue solver
  val @?= -11

case_AssertAtom :: IO ()
case_AssertAtom = do
  solver <- newSolver
  x0 <- newVar solver
  assertAtom solver (LA.constExpr 1 .<=. LA.varExpr x0)
  ret <- getLB solver x0
  ret @?= Just 1

  solver <- newSolver
  x0 <- newVar solver
  assertAtom solver (LA.varExpr x0 .>=. LA.constExpr 1)
  ret <- getLB solver x0
  ret @?= Just 1

  solver <- newSolver
  x0 <- newVar solver
  assertAtom solver (LA.constExpr 1 .>=. LA.varExpr x0)
  ret <- getUB solver x0
  ret @?= Just 1

  solver <- newSolver
  x0 <- newVar solver
  assertAtom solver (LA.varExpr x0 .<=. LA.constExpr 1)
  ret <- getUB solver x0
  ret @?= Just 1

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
