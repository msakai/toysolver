{-# LANGUAGE TemplateHaskell #-}
module Test.Simplex (simplexTestGroup) where

import Control.Monad
import Data.Default.Class
import Data.Ratio
import Data.VectorSpace
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH
import Text.Printf
import qualified ToySolver.Data.LA as LA
import ToySolver.Arith.Simplex

case_test1 :: Assertion
case_test1 = do
  solver <- newSolver
  x <- newVar solver
  y <- newVar solver
  z <- newVar solver
  assertAtom solver (LA.fromTerms [(7,x), (12,y), (31,z)] .==. LA.constant 17)
  assertAtom solver (LA.fromTerms [(3,x), (5,y), (14,z)]  .==. LA.constant 7)
  assertAtom solver (LA.var x .>=. LA.constant 1)
  assertAtom solver (LA.var x .<=. LA.constant 40)
  assertAtom solver (LA.var y .>=. LA.constant (-50))
  assertAtom solver (LA.var y .<=. LA.constant 50)

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

case_test2 :: Assertion
case_test2 = do
  solver <- newSolver
  x <- newVar solver
  y <- newVar solver
  assertAtom solver (LA.fromTerms [(11,x), (13,y)] .>=. LA.constant 27)
  assertAtom solver (LA.fromTerms [(11,x), (13,y)] .<=. LA.constant 45)
  assertAtom solver (LA.fromTerms [(7,x), (-9,y)] .>=. LA.constant (-10))
  assertAtom solver (LA.fromTerms [(7,x), (-9,y)] .<=. LA.constant 4)

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
case_test3 :: Assertion
case_test3 = do
  solver <- newSolver

  _ <- newVar solver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver

  setObj solver (LA.fromTerms [(-1,x1), (-2,x2), (-3,x3), (-1,x4)])

  assertAtom solver (LA.fromTerms [(-1,x1), (1,x2), (1,x3), (10,x4)] .<=. LA.constant 20)
  assertAtom solver (LA.fromTerms [(1,x1), (-3,x2), (1,x3)] .<=. LA.constant 30)
  assertAtom solver (LA.fromTerms [(1,x2), (-3.5,x4)] .==. LA.constant 0)

  assertAtom solver (LA.fromTerms [(1,x1)] .>=. LA.constant 0)
  assertAtom solver (LA.fromTerms [(1,x1)] .<=. LA.constant 40)
  assertAtom solver (LA.fromTerms [(1,x2)] .>=. LA.constant 0)
  assertAtom solver (LA.fromTerms [(1,x3)] .>=. LA.constant 0)
  assertAtom solver (LA.fromTerms [(1,x4)] .>=. LA.constant 2)
  assertAtom solver (LA.fromTerms [(1,x4)] .<=. LA.constant 3)

  ret1 <- check solver
  ret1 @?= True

  ret2 <- optimize solver def
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
case_test6 :: Assertion
case_test6 = do
  solver <- newSolver

  _  <- newVar solver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver

  assertLower solver x1 0
  assertLower solver x2 0
  assertLower solver x3 0
  assertAtom solver (LA.fromTerms [(1,x1),(2,x2),(3,x3)] .>=. LA.constant 5)
  assertAtom solver (LA.fromTerms [(2,x1),(2,x2),(1,x3)] .>=. LA.constant 6)

  setObj solver (LA.fromTerms [(3,x1),(4,x2),(5,x3)])
  setOptDir solver OptMin
  b <- isOptimal solver
  assertBool "should be optimal" $ b

  ret <- dualSimplex solver def
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
case_test7 :: Assertion
case_test7 = do
  solver <- newSolver

  _  <- newVar solver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver

  assertLower solver x1 0
  assertLower solver x2 0
  assertLower solver x3 0
  assertAtom solver (LA.fromTerms [(-1,x1),(-2,x2),(-3,x3)] .<=. LA.constant (-5))
  assertAtom solver (LA.fromTerms [(-2,x1),(-2,x2),(-1,x3)] .<=. LA.constant (-6))

  setObj solver (LA.fromTerms [(-3,x1),(-4,x2),(-5,x3)])
  setOptDir solver OptMax
  b <- isOptimal solver
  assertBool "should be optimal" $ b

  ret <- dualSimplex solver def
  ret @?= Optimum

  val <- getObjValue solver
  val @?= -11

case_AssertAtom :: Assertion
case_AssertAtom = do
  solver <- newSolver
  x0 <- newVar solver
  assertAtom solver (LA.constant 1 .<=. LA.var x0)
  ret <- getLB solver x0
  boundValue ret @?= Just 1

  solver <- newSolver
  x0 <- newVar solver
  assertAtom solver (LA.var x0 .>=. LA.constant 1)
  ret <- getLB solver x0
  boundValue ret @?= Just 1

  solver <- newSolver
  x0 <- newVar solver
  assertAtom solver (LA.constant 1 .>=. LA.var x0)
  ret <- getUB solver x0
  boundValue ret @?= Just 1

  solver <- newSolver
  x0 <- newVar solver
  assertAtom solver (LA.var x0 .<=. LA.constant 1)
  ret <- getUB solver x0
  boundValue ret @?= Just 1

------------------------------------------------------------------------

case_example_3_2 = do
  solver <- newSolver
  [x1,x2,x3] <- replicateM 3 (newVar solver)
  setOptDir solver OptMax
  setObj solver $ LA.fromTerms [(3,x1), (2,x2), (3,x3)]
  mapM_ (assertAtom solver) $
    [ LA.fromTerms [(2,x1), (1,x2), (1,x3)] .<=. LA.constant 2
    , LA.fromTerms [(1,x1), (2,x2), (3,x3)] .<=. LA.constant 5
    , LA.fromTerms [(2,x1), (2,x2), (1,x3)] .<=. LA.constant 6
    , LA.var x1 .>=. LA.constant 0
    , LA.var x2 .>=. LA.constant 0
    , LA.var x3 .>=. LA.constant 0
    ]

  ret <- optimize solver def
  ret @?= Optimum
  val <- getObjValue solver
  val @?= 27/5

  forM_ [(x1,1/5),(x2,0),(x3,8/5)] $ \(var,expected) -> do
    val <- getValue solver var
    val @?= expected

case_example_3_5 = do
  solver <- newSolver
  [x1,x2,x3,x4,x5] <- replicateM 5 (newVar solver)
  setOptDir solver OptMin
  setObj solver $ LA.fromTerms [(-2,x1), (4,x2), (7,x3), (1,x4), (5,x5)]
  mapM_ (assertAtom solver) $
    [ LA.fromTerms [(-1,x1), (1,x2), (2,x3), (1,x4), (2,x5)] .==. LA.constant 7
    , LA.fromTerms [(-1,x1), (2,x2), (3,x3), (1,x4), (1,x5)] .==. LA.constant 6
    , LA.fromTerms [(-1,x1), (1,x2), (1,x3), (2,x4), (1,x5)] .==. LA.constant 4
    , LA.var x2 .>=. LA.constant 0
    , LA.var x3 .>=. LA.constant 0
    , LA.var x4 .>=. LA.constant 0
    , LA.var x5 .>=. LA.constant 0
    ]

  ret <- optimize solver def
  ret @?= Optimum
  val <- getObjValue solver
  val @?= 19

  forM_ [(x1,-1),(x2,0),(x3,1),(x4,0),(x5,2)] $ \(var,expected) -> do
    val <- getValue solver var
    val @?= expected

case_example_4_1 = do
  solver <- newSolver
  [x1,x2] <- replicateM 2 (newVar solver)
  setOptDir solver OptMin
  setObj solver $ LA.fromTerms [(2,x1), (1,x2)]
  mapM_ (assertAtom solver) $
    [ LA.fromTerms [(-1,x1), (1,x2)] .>=. LA.constant 2
    , LA.fromTerms [( 1,x1), (1,x2)] .<=. LA.constant 1
    , LA.var x1 .>=. LA.constant 0
    , LA.var x2 .>=. LA.constant 0
    ]
  ret <- optimize solver def
  ret @?= Unsat

case_example_4_2 = do
  solver <- newSolver
  [x1,x2] <- replicateM 2 (newVar solver)
  setOptDir solver OptMax
  setObj solver $ LA.fromTerms [(2,x1), (1,x2)]
  mapM_ (assertAtom solver) $
    [ LA.fromTerms [(-1,x1), (-1,x2)] .<=. LA.constant 10
    , LA.fromTerms [( 2,x1), (-1,x2)] .<=. LA.constant 40
    , LA.var x1 .>=. LA.constant 0
    , LA.var x2 .>=. LA.constant 0
    ]
  ret <- optimize solver def
  ret @?= Unbounded

case_example_4_3 = do
  solver <- newSolver
  [x1,x2] <- replicateM 2 (newVar solver)
  setOptDir solver OptMax
  setObj solver $ LA.fromTerms [(6,x1), (-2,x2)]
  mapM_ (assertAtom solver) $
    [ LA.fromTerms [(2,x1), (-1,x2)] .<=. LA.constant 2
    , LA.var x1 .<=. LA.constant 4
    , LA.var x1 .>=. LA.constant 0
    , LA.var x2 .>=. LA.constant 0
    ]

  ret <- optimize solver def
  ret @?= Optimum
  val <- getObjValue solver
  val @?= 12

  forM_ [(x1,4),(x2,6)] $ \(var,expected) -> do
    val <- getValue solver var
    val @?= expected

case_example_4_5 = do
  solver <- newSolver
  [x1,x2] <- replicateM 2 (newVar solver)
  setOptDir solver OptMax
  setObj solver $ LA.fromTerms [(2,x1), (1,x2)]
  mapM_ (assertAtom solver) $
    [ LA.fromTerms [(4,x1), ( 3,x2)] .<=. LA.constant 12
    , LA.fromTerms [(4,x1), ( 1,x2)] .<=. LA.constant 8
    , LA.fromTerms [(4,x1), (-1,x2)] .<=. LA.constant 8
    , LA.var x1 .>=. LA.constant 0
    , LA.var x2 .>=. LA.constant 0
    ]

  ret <- optimize solver def
  ret @?= Optimum
  val <- getObjValue solver
  val @?= 5

  forM_ [(x1,3/2),(x2,2)] $ \(var,expected) -> do
    val <- getValue solver var
    val @?= expected

case_example_4_6 = do
  solver <- newSolver
  [x1,x2,x3,x4] <- replicateM 4 (newVar solver)
  setOptDir solver OptMax
  setObj solver $ LA.fromTerms [(20,x1), (1/2,x2), (-6,x3), (3/4,x4)]
  mapM_ (assertAtom solver) $
    [ LA.var x1 .<=. LA.constant 2
    , LA.fromTerms [( 8,x1), (  -1,x2), (9,x3), (1/4, x4)] .<=. LA.constant 16
    , LA.fromTerms [(12,x1), (-1/2,x2), (3,x3), (1/2, x4)] .<=. LA.constant 24
    , LA.var x2 .<=. LA.constant 1
    , LA.var x1 .>=. LA.constant 0
    , LA.var x2 .>=. LA.constant 0
    , LA.var x3 .>=. LA.constant 0
    , LA.var x4 .>=. LA.constant 0
    ]

  ret <- optimize solver def
  ret @?= Optimum
  val <- getObjValue solver
  val @?= 165/4

  forM_ [(x1,2),(x2,1),(x3,0),(x4,1)] $ \(var,expected) -> do
    val <- getValue solver var
    val @?= expected

case_example_4_7 = do
  solver <- newSolver
  [x1,x2,x3,x4] <- replicateM 4 (newVar solver)
  setOptDir solver OptMax
  setObj solver $ LA.fromTerms [(1,x1), (1.5,x2), (5,x3), (2,x4)]
  mapM_ (assertAtom solver) $
    [ LA.fromTerms [(3,x1), (2,x2), ( 1,x3), (4,x4)] .<=. LA.constant 6
    , LA.fromTerms [(2,x1), (1,x2), ( 5,x3), (1,x4)] .<=. LA.constant 4
    , LA.fromTerms [(2,x1), (6,x2), (-4,x3), (8,x4)] .==. LA.constant 0
    , LA.fromTerms [(1,x1), (3,x2), (-2,x3), (4,x4)] .==. LA.constant 0
    , LA.var x1 .>=. LA.constant 0
    , LA.var x2 .>=. LA.constant 0
    , LA.var x3 .>=. LA.constant 0
    , LA.var x4 .>=. LA.constant 0
    ]

  ret <- optimize solver def
  ret @?= Optimum
  val <- getObjValue solver
  val @?= 48/11

  forM_ [(x1,0),(x2,0),(x3,8/11),(x4,4/11)] $ \(var,expected) -> do
    val <- getValue solver var
    val @?= expected

-- 退化して巡回の起こるKuhnの7変数3制約の例
case_kuhn_7_3 = do
  solver <- newSolver
  [x1,x2,x3,x4,x5,x6,x7] <- replicateM 7 (newVar solver)
  setOptDir solver OptMin
  setObj solver $ LA.fromTerms [(-2,x4),(-3,x5),(1,x6),(12,x7)]
  mapM_ (assertAtom solver) $
    [ LA.fromTerms [(1,x1), ( -2,x4), (-9,x5), (   1,x6), (  9,x7)] .==. LA.constant 0
    , LA.fromTerms [(1,x2), (1/3,x4), ( 1,x5), (-1/3,x6), ( -2,x7)] .==. LA.constant 0
    , LA.fromTerms [(1,x3), (  2,x4), ( 3,x5), (  -1,x6), (-12,x7)] .==. LA.constant 2
    , LA.var x1 .>=. LA.constant 0
    , LA.var x2 .>=. LA.constant 0
    , LA.var x3 .>=. LA.constant 0
    , LA.var x4 .>=. LA.constant 0
    , LA.var x5 .>=. LA.constant 0
    , LA.var x6 .>=. LA.constant 0
    , LA.var x7 .>=. LA.constant 0
    ]

  ret <- optimize solver def
  ret @?= Optimum
  val <- getObjValue solver
  val @?= -2

  forM_ [(x1,2),(x2,0),(x3,0),(x4,2),(x5,0),(x6,2),(x7,0)] $ \(var,expected) -> do
    val <- getValue solver var
    val @?= expected

------------------------------------------------------------------------
-- Test harness

simplexTestGroup :: TestTree
simplexTestGroup = $(testGroupGenerator)
