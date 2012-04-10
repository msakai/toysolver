module Main (main) where

import Control.Monad
import Test.HUnit hiding (Test)
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.Providers.HUnit
import SAT

-- should be SAT
test1 :: IO ()
test1 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [literal x1 True,  literal x2 True]  -- x1 or x2
  addClause solver [literal x1 True,  literal x2 False] -- x1 or not x2
  addClause solver [literal x1 False, literal x2 False] -- not x1 or not x2
  ret <- solve solver
  assertEqual "test1" True ret

-- shuld be UNSAT
test2 :: IO ()
test2 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [literal x1 True,  literal x2 True]  -- x1 or x2
  addClause solver [literal x1 False, literal x2 True]  -- not x1 or x2
  addClause solver [literal x1 True,  literal x2 False] -- x1 or not x2
  addClause solver [literal x1 False, literal x2 False] -- not x2 or not x2
  ret <- solve solver
  assertEqual "test2" False ret

-- top level でいきなり矛盾
test3 :: IO ()
test3 = do
  solver <- newSolver
  x1 <- newVar solver
  addClause solver [literal x1 True]
  addClause solver [literal x1 False]
  ret <- solve solver -- unsat
  assertEqual "test3" False ret  

-- incremental に制約を追加
test4 :: IO ()
test4 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [literal x1 True,  literal x2 True]  -- x1 or x2
  addClause solver [literal x1 True,  literal x2 False] -- x1 or not x2
  addClause solver [literal x1 False, literal x2 False] -- not x1 or not x2
  ret <- solve solver -- sat
  assertEqual "test4a" True ret

  addClause solver [literal x1 False, literal x2 True]  -- not x1 or x2
  ret <- solve solver -- unsat
  assertEqual "test4a" False ret

-- 自明に真な節
test5 :: IO ()
test5 = do
  solver <- newSolver
  x1 <- newVar solver
  addClause solver [x1, -x1] -- x1 or not x1
  ret <- solve solver
  assertEqual "test5" True ret

-- 冗長な節
test6 :: IO ()
test6 = do
  solver <- newSolver
  x1 <- newVar solver
  addClause solver [x1,x1] -- x1 or x1
  ret <- solve solver
  assertEqual "test6" True ret

testInstantiateClause :: IO ()
testInstantiateClause = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [x1]
  addClause solver [x1,x2]
  addClause solver [-x1,x2]
  ret <- solve solver
  assertEqual "InstantiateClause" True ret

testInstantiateAtLeast :: IO ()
testInstantiateAtLeast = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver
  addClause solver [x1]

  addAtLeast solver [x1,x2,x3,x4] 2
  ret <- solve solver
  assertEqual "testInstantiateClause1" True ret

  addAtLeast solver [-x1,-x2,-x3,-x4] 2
  ret <- solve solver
  assertEqual "testInstantiateClause2" True ret

testAtLeast1 :: IO ()
testAtLeast1 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  addAtLeast solver [x1,x2,x3] 2
  addAtLeast solver [-x1,-x2,-x3] 2
  ret <- solve solver -- unsat
  assertEqual "testAtLeast1" False ret

testAtLeast2 :: IO ()
testAtLeast2 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver
  addAtLeast solver [x1,x2,x3,x4] 2
  addClause solver [-x1,-x2]
  addClause solver [-x1,-x3]
  ret <- solve solver
  assertEqual "testAtLeast2" True ret

testAtLeast3 :: IO ()
testAtLeast3 = do
  forM_ [(-1) .. 3] $ \n -> do
    solver <- newSolver
    x1 <- newVar solver
    x2 <- newVar solver
    addAtLeast solver [x1,x2] n
    ret <- solve solver
    assertEqual ("testAtLeast3_" ++ show n) (n <= 2) ret

-- from http://www.cril.univ-artois.fr/PB11/format.pdf
testPB1 :: IO ()
testPB1 = do
  solver <- newSolver

  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver
  x5 <- newVar solver

  addPBAtLeast solver [(1,x1),(4,x2),(-2,x5)] 2
  addPBAtLeast solver [(-1,x1),(4,x2),(-2,x5)] 3
  addPBAtLeast solver [(12345678901234567890,x4),(4,x3)] 10
  addPBExactly solver [(2,x2),(3,x4),(2,x1),(3,x5)] 5

  ret <- solve solver
  assertEqual "testPB1" True ret

-- 一部の変数を否定に置き換えたもの
testPB2 :: IO ()
testPB2 = do
  solver <- newSolver

  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver
  x5 <- newVar solver

  addPBAtLeast solver [(1,x1),(4,-x2),(-2,x5)] 2
  addPBAtLeast solver [(-1,x1),(4,-x2),(-2,x5)] 3
  addPBAtLeast solver [(12345678901234567890,-x4),(4,x3)] 10
  addPBExactly solver [(2,-x2),(3,-x4),(2,x1),(3,x5)] 5

  ret <- solve solver
  assertEqual "testPB2" True ret

-- いきなり矛盾したPB制約
testPB3 :: IO ()
testPB3 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addPBAtLeast solver [(2,x1),(3,x2)] 6
  ret <- solve solver
  assertEqual "testPB3" False ret

testPB4 :: IO ()
testPB4 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addPBAtLeast solver [(1,x1),(3,x2)] 3
  addClause solver [-x1]
  ret <- solve solver
  assertEqual "testPB4" True ret

testAssumption :: IO ()
testAssumption = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  addClause solver [x1, x2]       -- x1 or x2
  addClause solver [x1, -x2]      -- x1 or not x2
  addClause solver [-x1, -x2]     -- not x1 or not x2
  addClause solver [-x3, -x1, x2] -- not x3 or not x1 or x2

  ret <- solve solver -- sat
  assertEqual "testAssumpttion1" True ret

  ret <- solveWith solver [x3] -- unsat
  assertEqual "testAssumpttion2" False ret  

  ret <- solve solver -- sat
  assertEqual "testAssumpttion3" True ret


testAssumption2 :: IO ()
testAssumption2 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [x1]      -- x1
  addClause solver [-x1, x2] -- -x1 or x2
  ret <- solveWith solver [x2]
  assertEqual "already assigned vairable is assumed" True ret

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = defaultMain tests

tests :: [Test]
tests =
    [ testCase "test1" test1
    , testCase "test2" test2
    , testCase "test3" test3
    , testCase "test4" test4
    , testCase "test5" test5
    , testCase "test6" test6
    , testCase "testInstantiateClause" testInstantiateClause
    , testCase "testInstantiateAtLeast" testInstantiateAtLeast
    , testCase "testAtLeast1" testAtLeast1
    , testCase "testAtLeast2" testAtLeast2
    , testCase "testAtLeast3" testAtLeast3
    , testCase "testPB1" testPB1
    , testCase "testPB2" testPB2
    , testCase "testPB3" testPB3
    , testCase "testPB4" testPB4
    , testCase "testAssumption" testAssumption
    , testCase "testAssumption2" testAssumption2
    ]
{-
    [ testProperty "bernstein" pHash
    , testGroup "text"
      [ testProperty "text/strict" pText
      , testProperty "text/lazy" pTextLazy
      , testProperty "rechunk" pRechunk
      , testProperty "text/rechunked" pLazyRechunked
      ]
    ]
-}
