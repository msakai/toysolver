{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.SAT (satTestGroup) where

import Control.Exception
import Control.Monad
import Data.Array.IArray
import Data.Default.Class
import qualified Data.IntSet as IntSet
import Data.IORef
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V
import qualified System.Random.MWC as Rand

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import ToySolver.Data.LBool
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.SAT as SAT

import Test.SAT.Utils

prop_solveCNF :: Property
prop_solveCNF = QM.monadicIO $ do
  cnf <- QM.pick arbitraryCNF
  solver <- arbitrarySolver
  ret <- QM.run $ solveCNF solver cnf
  case ret of
    Just m -> QM.assert $ evalCNF m cnf
    Nothing -> do
      forM_ (allAssignments (CNF.cnfNumVars cnf)) $ \m -> do
        QM.assert $ not (evalCNF m cnf)

prop_solvePB :: Property
prop_solvePB = QM.monadicIO $ do
  prob@(nv,_) <- QM.pick arbitraryPB
  solver <- arbitrarySolver
  ret <- QM.run $ solvePB solver prob
  case ret of
    Just m -> QM.assert $ evalPB m prob
    Nothing -> do
      forM_ (allAssignments nv) $ \m -> do
        QM.assert $ not (evalPB m prob)

prop_optimizePBO :: Property
prop_optimizePBO = QM.monadicIO $ do
  prob@(nv,_) <- QM.pick arbitraryPB
  obj <- QM.pick $ arbitraryPBLinSum nv
  solver <- arbitrarySolver
  opt <- arbitraryOptimizer solver obj
  ret <- QM.run $ optimizePBO solver opt prob
  case ret of
    Just (m, v) -> do
      QM.assert $ evalPB m prob
      QM.assert $ SAT.evalPBLinSum m obj == v
      forM_ (allAssignments nv) $ \m2 -> do
        QM.assert $ not (evalPB m2 prob) || SAT.evalPBLinSum m obj <= SAT.evalPBLinSum m2 obj
    Nothing -> do
      forM_ (allAssignments nv) $ \m -> do
        QM.assert $ not (evalPB m prob)

prop_solvePBNLC :: Property
prop_solvePBNLC = QM.monadicIO $ do
  prob@(nv,_) <- QM.pick arbitraryPBNLC
  solver <- arbitrarySolver
  ret <- QM.run $ solvePBNLC solver prob
  case ret of
    Just m -> QM.assert $ evalPBNLC m prob
    Nothing -> do
      forM_ (allAssignments nv) $ \m -> do
        QM.assert $ not (evalPBNLC m prob)


prop_solveXOR :: Property
prop_solveXOR = QM.monadicIO $ do
  prob@(nv,_) <- QM.pick arbitraryXOR
  solver <- arbitrarySolver
  ret <- QM.run $ solveXOR solver prob
  case ret of
    Just m -> QM.assert $ evalXOR m prob
    Nothing -> do
      forM_ (allAssignments nv) $ \m -> do
        QM.assert $ not (evalXOR m prob)

solveXOR :: SAT.Solver -> (Int,[SAT.XORClause]) -> IO (Maybe SAT.Model)
solveXOR solver (nv,cs) = do
  SAT.modifyConfig solver $ \config -> config{ SAT.configCheckModel = True }
  SAT.newVars_ solver nv
  forM_ cs $ \c -> SAT.addXORClause solver (fst c) (snd c)
  ret <- SAT.solve solver
  if ret then do
    m <- SAT.getModel solver
    return (Just m)
  else do
    return Nothing

-- should be SAT
case_solve_SAT :: Assertion
case_solve_SAT = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addClause solver [x1, x2]  -- x1 or x2
  SAT.addClause solver [x1, -x2] -- x1 or not x2
  SAT.addClause solver [-x1, -x2] -- not x1 or not x2
  ret <- SAT.solve solver
  ret @?= True

-- shuld be UNSAT
case_solve_UNSAT :: Assertion
case_solve_UNSAT = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addClause solver [x1,  x2]  -- x1 or x2
  SAT.addClause solver [-x1, x2]  -- not x1 or x2
  SAT.addClause solver [x1,  -x2] -- x1 or not x2
  SAT.addClause solver [-x1, -x2] -- not x2 or not x2
  ret <- SAT.solve solver
  ret @?= False

-- top level でいきなり矛盾
case_root_inconsistent :: Assertion
case_root_inconsistent = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  SAT.addClause solver [x1]
  SAT.addClause solver [-x1]
  ret <- SAT.solve solver -- unsat
  ret @?= False

-- incremental に制約を追加
case_incremental_solving :: Assertion
case_incremental_solving = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addClause solver [x1,  x2]  -- x1 or x2
  SAT.addClause solver [x1,  -x2] -- x1 or not x2
  SAT.addClause solver [-x1, -x2] -- not x1 or not x2
  ret <- SAT.solve solver -- sat
  ret @?= True

  SAT.addClause solver [-x1, x2]  -- not x1 or x2
  ret2 <- SAT.solve solver -- unsat
  ret2 @?= False

-- 制約なし
case_empty_constraint :: Assertion
case_empty_constraint = do
  solver <- SAT.newSolver
  ret <- SAT.solve solver
  ret @?= True

-- 空の節
case_empty_claue :: Assertion
case_empty_claue = do
  solver <- SAT.newSolver
  SAT.addClause solver []
  ret <- SAT.solve solver
  ret @?= False

-- 自明に真な節
case_excluded_middle_claue :: Assertion
case_excluded_middle_claue = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  SAT.addClause solver [x1, -x1] -- x1 or not x1
  ret <- SAT.solve solver
  ret @?= True

-- 冗長な節
case_redundant_clause :: Assertion
case_redundant_clause = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  SAT.addClause solver [x1,x1] -- x1 or x1
  ret <- SAT.solve solver
  ret @?= True

case_instantiateClause :: Assertion
case_instantiateClause = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addClause solver [x1]
  SAT.addClause solver [x1,x2]
  SAT.addClause solver [-x1,x2]
  ret <- SAT.solve solver
  ret @?= True

case_instantiateAtLeast :: Assertion
case_instantiateAtLeast = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  x4 <- SAT.newVar solver
  SAT.addClause solver [x1]

  SAT.addAtLeast solver [x1,x2,x3,x4] 2
  ret <- SAT.solve solver
  ret @?= True

  SAT.addAtLeast solver [-x1,-x2,-x3,-x4] 2
  ret2 <- SAT.solve solver
  ret2 @?= True

case_inconsistent_AtLeast :: Assertion
case_inconsistent_AtLeast = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addAtLeast solver [x1,x2] 3
  ret <- SAT.solve solver -- unsat
  ret @?= False

case_trivial_AtLeast :: Assertion
case_trivial_AtLeast = do
  do
    solver <- SAT.newSolver
    x1 <- SAT.newVar solver
    x2 <- SAT.newVar solver
    SAT.addAtLeast solver [x1,x2] 0
    ret <- SAT.solve solver
    ret @?= True
  do
    solver <- SAT.newSolver
    x1 <- SAT.newVar solver
    x2 <- SAT.newVar solver
    SAT.addAtLeast solver [x1,x2] (-1)
    ret <- SAT.solve solver
    ret @?= True

case_AtLeast_1 :: Assertion
case_AtLeast_1 = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  SAT.addAtLeast solver [x1,x2,x3] 2
  SAT.addAtLeast solver [-x1,-x2,-x3] 2
  ret <- SAT.solve solver -- unsat
  ret @?= False

case_AtLeast_2 :: Assertion
case_AtLeast_2 = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  x4 <- SAT.newVar solver
  SAT.addAtLeast solver [x1,x2,x3,x4] 2
  SAT.addClause solver [-x1,-x2]
  SAT.addClause solver [-x1,-x3]
  ret <- SAT.solve solver
  ret @?= True

case_AtLeast_3 :: Assertion
case_AtLeast_3 = do
  forM_ [(-1) .. 3] $ \n -> do
    solver <- SAT.newSolver
    x1 <- SAT.newVar solver
    x2 <- SAT.newVar solver
    SAT.addAtLeast solver [x1,x2] n
    ret <- SAT.solve solver
    assertEqual ("case_AtLeast3_" ++ show n) (n <= 2) ret

-- from http://www.cril.univ-artois.fr/PB11/format.pdf
case_PB_sample1 :: Assertion
case_PB_sample1 = do
  solver <- SAT.newSolver

  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  x4 <- SAT.newVar solver
  x5 <- SAT.newVar solver

  SAT.addPBAtLeast solver [(1,x1),(4,x2),(-2,x5)] 2
  SAT.addPBAtLeast solver [(-1,x1),(4,x2),(-2,x5)] 3
  SAT.addPBAtLeast solver [(12345678901234567890,x4),(4,x3)] 10
  SAT.addPBExactly solver [(2,x2),(3,x4),(2,x1),(3,x5)] 5

  ret <- SAT.solve solver
  ret @?= True

-- 一部の変数を否定に置き換えたもの
case_PB_sample1' :: Assertion
case_PB_sample1' = do
  solver <- SAT.newSolver

  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  x4 <- SAT.newVar solver
  x5 <- SAT.newVar solver

  SAT.addPBAtLeast solver [(1,x1),(4,-x2),(-2,x5)] 2
  SAT.addPBAtLeast solver [(-1,x1),(4,-x2),(-2,x5)] 3
  SAT.addPBAtLeast solver [(12345678901234567890,-x4),(4,x3)] 10
  SAT.addPBExactly solver [(2,-x2),(3,-x4),(2,x1),(3,x5)] 5

  ret <- SAT.solve solver
  ret @?= True

-- いきなり矛盾したPB制約
case_root_inconsistent_PB :: Assertion
case_root_inconsistent_PB = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addPBAtLeast solver [(2,x1),(3,x2)] 6
  ret <- SAT.solve solver
  ret @?= False

case_pb_propagate :: Assertion
case_pb_propagate = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addPBAtLeast solver [(1,x1),(3,x2)] 3
  SAT.addClause solver [-x1]
  ret <- SAT.solve solver
  ret @?= True

case_solveWith_1 :: Assertion
case_solveWith_1 = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  SAT.addClause solver [x1, x2]       -- x1 or x2
  SAT.addClause solver [x1, -x2]      -- x1 or not x2
  SAT.addClause solver [-x1, -x2]     -- not x1 or not x2
  SAT.addClause solver [-x3, -x1, x2] -- not x3 or not x1 or x2

  ret2 <- SAT.solve solver -- sat
  ret2 @?= True

  ret3 <- SAT.solveWith solver [x3] -- unsat
  ret3 @?= False

  ret4 <- SAT.solve solver -- sat
  ret4 @?= True

case_solveWith_2 :: Assertion
case_solveWith_2 = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addClause solver [-x1, x2] -- -x1 or x2
  SAT.addClause solver [x1]      -- x1

  ret <- SAT.solveWith solver [x2]
  ret @?= True

  ret2 <- SAT.solveWith solver [-x2]
  ret2 @?= False

case_getVarFixed :: Assertion
case_getVarFixed = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addClause solver [x1,x2]

  ret <- SAT.getVarFixed solver x1
  ret @?= lUndef

  SAT.addClause solver [-x1]

  ret2 <- SAT.getVarFixed solver x1
  ret2 @?= lFalse

  ret3 <- SAT.getLitFixed solver (-x1)
  ret3 @?= lTrue

  ret4 <- SAT.getLitFixed solver x2
  ret4 @?= lTrue

case_getAssumptionsImplications_case1 :: Assertion
case_getAssumptionsImplications_case1 = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  SAT.addClause solver [x1,x2,x3]

  SAT.addClause solver [-x1]
  ret <- SAT.solveWith solver [-x2]
  ret @?= True
  xs <- SAT.getAssumptionsImplications solver
  xs @?= IntSet.singleton x3

prop_getAssumptionsImplications :: Property
prop_getAssumptionsImplications = QM.monadicIO $ do
  cnf <- QM.pick arbitraryCNF
  solver <- arbitrarySolver
  ls <- QM.pick $ liftM concat $ mapM (\v -> elements [[],[-v],[v]]) [1..CNF.cnfNumVars cnf]
  ret <- QM.run $ do
    SAT.newVars_ solver (CNF.cnfNumVars cnf)
    forM_ (CNF.cnfClauses cnf) $ \c -> SAT.addClause solver (SAT.unpackClause c)
    SAT.solveWith solver ls
  when ret $ do
    xs <- liftM IntSet.toList $ QM.run $ SAT.getAssumptionsImplications solver
    forM_ xs $ \x -> do
      ret2 <- QM.run $ SAT.solveWith solver (-x : ls)
      QM.assert $ not ret2

------------------------------------------------------------------------

case_xor_case1 :: Assertion
case_xor_case1 = do
  solver <- SAT.newSolver
  SAT.modifyConfig solver $ \config -> config{ SAT.configCheckModel = True }
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  SAT.addXORClause solver [x1, x2] True -- x1 ⊕ x2 = True
  SAT.addXORClause solver [x2, x3] True -- x2 ⊕ x3 = True
  SAT.addXORClause solver [x3, x1] True -- x3 ⊕ x1 = True
  ret <- SAT.solve solver
  ret @?= False

case_xor_case2 :: Assertion
case_xor_case2 = do
  solver <- SAT.newSolver
  SAT.modifyConfig solver $ \config -> config{ SAT.configCheckModel = True }
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  SAT.addXORClause solver [x1, x2] True -- x1 ⊕ x2 = True
  SAT.addXORClause solver [x1, x3] True -- x1 ⊕ x3 = True
  SAT.addClause solver [x2]

  ret <- SAT.solve solver
  ret @?= True
  m <- SAT.getModel solver
  m ! x1 @?= False
  m ! x2 @?= True
  m ! x3 @?= True

case_xor_case3 :: Assertion
case_xor_case3 = do
  solver <- SAT.newSolver
  SAT.modifyConfig solver $ \config -> config{ SAT.configCheckModel = True }
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- SAT.newVar solver
  x4 <- SAT.newVar solver
  SAT.addXORClause solver [x1,x2,x3,x4] True
  SAT.addAtLeast solver [x1,x2,x3,x4] 2
  ret <- SAT.solve solver
  ret @?= True

------------------------------------------------------------------------

-- from "Pueblo: A Hybrid Pseudo-Boolean SAT Solver"
-- clauseがunitになるレベルで、PB制約が違反状態のままという例。
case_hybridLearning_1 :: Assertion
case_hybridLearning_1 = do
  solver <- SAT.newSolver
  [x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11] <- replicateM 11 (SAT.newVar solver)

  SAT.addClause solver [x11, x10, x9] -- C1
  SAT.addClause solver [x8, x7, x6]   -- C2
  SAT.addClause solver [x5, x4, x3]   -- C3
  SAT.addAtLeast solver [-x2, -x5, -x8, -x11] 3 -- C4
  SAT.addAtLeast solver [-x1, -x4, -x7, -x10] 3 -- C5

  replicateM_ 3 (SAT.varBumpActivity solver x3)
  SAT.setVarPolarity solver x3 False

  replicateM_ 2 (SAT.varBumpActivity solver x6)
  SAT.setVarPolarity solver x6 False

  replicateM_ 1 (SAT.varBumpActivity solver x9)
  SAT.setVarPolarity solver x9 False

  SAT.setVarPolarity solver x1 True

  SAT.modifyConfig solver $ \config -> config{ SAT.configLearningStrategy = SAT.LearningHybrid }
  ret <- SAT.solve solver
  ret @?= True

-- from "Pueblo: A Hybrid Pseudo-Boolean SAT Solver"
-- clauseがunitになるレベルで、PB制約が違反状態のままという例。
-- さらに、学習したPB制約はunitにはならない。
case_hybridLearning_2 :: Assertion
case_hybridLearning_2 = do
  solver <- SAT.newSolver
  [x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12] <- replicateM 12 (SAT.newVar solver)

  SAT.addClause solver [x11, x10, x9] -- C1
  SAT.addClause solver [x8, x7, x6]   -- C2
  SAT.addClause solver [x5, x4, x3]   -- C3
  SAT.addAtLeast solver [-x2, -x5, -x8, -x11] 3 -- C4
  SAT.addAtLeast solver [-x1, -x4, -x7, -x10] 3 -- C5

  SAT.addClause solver [x12, -x3]
  SAT.addClause solver [x12, -x6]
  SAT.addClause solver [x12, -x9]

  SAT.varBumpActivity solver x12
  SAT.setVarPolarity solver x12 False

  SAT.modifyConfig solver $ \config -> config{ SAT.configLearningStrategy = SAT.LearningHybrid }
  ret <- SAT.solve solver
  ret @?= True

-- regression test for the bug triggered by normalized-blast-floppy1-8.ucl.opb.bz2
case_addPBAtLeast_regression :: Assertion
case_addPBAtLeast_regression = do
  solver <- SAT.newSolver
  [x1,x2,x3,x4] <- replicateM 4 (SAT.newVar solver)
  SAT.addClause solver [-x1]
  SAT.addClause solver [-x2, -x3]
  SAT.addClause solver [-x2, -x4]
  SAT.addPBAtLeast solver [(1,x1),(2,x2),(1,x3),(1,x4)] 3
  ret <- SAT.solve solver
  ret @?= False

-- https://github.com/msakai/toysolver/issues/22
case_issue22 :: Assertion
case_issue22 = do
  let config = def
        { SAT.configLearningStrategy = SAT.LearningHybrid
        , SAT.configCCMin = 2
        , SAT.configBranchingStrategy = SAT.BranchingLRB
        , SAT.configRandomFreq = 0.2816351099559239
        , SAT.configPBHandlerType = SAT.PBHandlerTypeCounter
        }
  solver <- SAT.newSolverWithConfig config
  _ <- SAT.newVars solver 14
  SAT.addClause solver [-7,-1]
  SAT.addClause solver [-9,-4]
  SAT.addClause solver [-9,1]
  SAT.addClause solver [-10,-1]
  SAT.addClause solver [-11,-1]
  SAT.addClause solver [-12,-4]
  SAT.addClause solver [-12,4]
  SAT.addClause solver [-13,-3]
  SAT.addClause solver [-13,-1]
  SAT.addClause solver [-13,3]
  SAT.addClause solver [-14,-1]
  SAT.addPBAtLeast solver [ (1,-14), (10,13), (7,12), (13,-11), (14,-10), (16,9), (8,8), (9,-7)]   38
  SAT.addPBAtLeast solver [(-1,-14),(-10,13),(-7,12),(-13,-11),(-14,-10),(-16,9),(-8,8),(-9,-7)] (-38)
  SAT.setRandomGen solver =<< Rand.initialize (V.singleton 71)
  _ <- SAT.solve solver
  return ()
{-
Scenario:
decide 4@1
deduce -12 by [-12,-4]
deduce -9 by [-9,-4]
decide 1@2
deduce -14 by [-14,-1]
deduce -13 by [-13,-1]
deduce -11 by [-11,-1]
deduce -10 by [-10,-1]
deduce -7 by [-7,-1]
deduce 8 by [(16,9),(14,-10),(13,-11),(10,13),(9,-7),(8,8),(7,12),(1,-14)] >= 38
conflict: [(16,-9),(14,10),(13,11),(10,-13),(9,7),(8,-8),(7,-12),(1,14)] >= 40
conflict analysis yields
  [-1,9,12] @1, and
  [(1,14),(2,-13),(1,12),(8,-9),(17,-1)],17) >= 17 @1 (but it should be @0)
backtrack to @1
deduce -1 by [-1,9,12]
decide 3@3
deduce -13 by [-13,-3]
deduce -10, -11, -7, 8 by [(16,9),(14,-10),(13,-11),(10,13),(9,-7),(8,8),(7,12),(1,-14)] >= 38
conflict [(16,-9),(14,10),(13,11),(10,-13),(9,7),(8,-8),(7,-12),(1,14)] >= 40
conflict analysis yields
  [13,9,12] @1 and
  [(1,14),(7,13),(7,12),(7,9)] >= 7 @1 (but it should be @0)
backtrack to @1
deduce 13 by [13,9,12]
deduce 3 by [3,-13]
conflict [-3,-13]
conflict analysis yields
  -13 @ 0
decide -7@1
decide -14@2
deduce -1 by [(17,-1),(8,-9),(2,-13),(1,14),(1,12)] >= 17
deduce -9 by [-9,1]
deduce 12 by [12,9,13]
deduce 4 by [4,-12]
conflict: [-4,-12]
conflict analysis yields [] and that causes error
-}

------------------------------------------------------------------------

pigeonHole :: SAT.Solver -> Integer -> Integer -> IO ()
pigeonHole solver p h = do
  vs <- liftM Map.fromList $ forM [(i,j) | i <- [1..p], j <- [1..h]]  $ \(i,j) -> do
    v <- SAT.newVar solver
    return ((i,j), v)
  forM_ [1..p] $ \i -> do
    SAT.addAtLeast solver [vs Map.! (i,j) | j <- [1..h]] 1
  forM_ [1..h] $ \j -> do
    SAT.addAtMost solver [vs Map.! (i,j) | i<-[1..p]] 1
  return ()

case_setTerminateCallback :: IO ()
case_setTerminateCallback = do
  solver <- SAT.newSolver
  SAT.setTerminateCallback solver (return True)

  pigeonHole solver 5 4

  m <- try (SAT.solve solver)
  case m of
    Left (_ :: SAT.Canceled) -> return ()
    Right x -> assertFailure ("Canceled should be thrown: " ++ show x)

case_clearTerminateCallback :: IO ()
case_clearTerminateCallback = do
  solver <- SAT.newSolver
  SAT.setTerminateCallback solver (return True)

  pigeonHole solver 5 4

  SAT.clearTerminateCallback solver
  _ <- SAT.solve solver
  return ()

case_setLearnCallback :: IO ()
case_setLearnCallback = do
  solver <- SAT.newSolver
  learntRef <- newIORef []
  SAT.setLearnCallback solver (\clause -> modifyIORef learntRef (clause:))

  pigeonHole solver 5 4

  _ <- SAT.solve solver
  learnt <- readIORef learntRef
  assertBool "learn callback should have been called" (not (null learnt))

case_clearLearnCallback :: IO ()
case_clearLearnCallback = do
  solver <- SAT.newSolver
  learntRef <- newIORef []
  SAT.setLearnCallback solver (\clause -> modifyIORef learntRef (clause:))

  pigeonHole solver 5 4

  SAT.clearLearnCallback solver
  _ <- SAT.solve solver
  learnt <- readIORef learntRef
  assertBool "learn callback should not have been called" (null learnt)

------------------------------------------------------------------------

prop_SOS2 :: Property
prop_SOS2 = QM.monadicIO $ do
  cnf <- QM.pick arbitraryCNF
  sos2 <- QM.pick $ do
    n <- choose (0, CNF.cnfNumVars cnf)
    replicateM n (arbitraryLit (CNF.cnfNumVars cnf))

  solver <- arbitrarySolver
  ret <- QM.run $ do
    SAT.newVars_ solver (CNF.cnfNumVars cnf)
    forM_ (CNF.cnfClauses cnf) $ \c -> SAT.addClause solver (SAT.unpackClause c)
    SAT.addSOS2 solver sos2
    ret <- SAT.solve solver
    if ret then do
      m <- SAT.getModel solver
      return (Just m)
    else do
      return Nothing

  case ret of
    Just m -> QM.assert $ evalCNF m cnf && SAT.evalSOS2 m sos2
    Nothing -> do
      forM_ (allAssignments (CNF.cnfNumVars cnf)) $ \m -> do
        QM.assert $ not (evalCNF m cnf && SAT.evalSOS2 m sos2)

------------------------------------------------------------------------
-- Test harness

satTestGroup :: TestTree
satTestGroup = $(testGroupGenerator)
