module Main (main) where

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
    , testCase "testAtLeast1" testAtLeast1
    , testCase "testAtLeast2" testAtLeast2
    , testCase "testPB1" testPB1
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
