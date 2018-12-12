{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, FlexibleContexts #-}
module Test.SAT (satTestGroup) where

import Control.Applicative
import Control.Monad
import Data.Array.IArray
import Data.Default.Class
import Data.List
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
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
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.MUS as MUS
import qualified ToySolver.SAT.MUS.Enum as MUSEnum

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
  ret <- SAT.solve solver -- unsat
  ret @?= False

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
  ret <- SAT.solve solver
  ret @?= True

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
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addAtLeast solver [x1,x2] 0
  ret <- SAT.solve solver
  ret @?= True

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

  ret <- SAT.solve solver -- sat
  ret @?= True

  ret <- SAT.solveWith solver [x3] -- unsat
  ret @?= False

  ret <- SAT.solve solver -- sat
  ret @?= True

case_solveWith_2 :: Assertion
case_solveWith_2 = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addClause solver [-x1, x2] -- -x1 or x2
  SAT.addClause solver [x1]      -- x1

  ret <- SAT.solveWith solver [x2]
  ret @?= True

  ret <- SAT.solveWith solver [-x2]
  ret @?= False

case_getVarFixed :: Assertion
case_getVarFixed = do
  solver <- SAT.newSolver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  SAT.addClause solver [x1,x2]

  ret <- SAT.getVarFixed solver x1
  ret @?= lUndef

  SAT.addClause solver [-x1]
  
  ret <- SAT.getVarFixed solver x1
  ret @?= lFalse

  ret <- SAT.getLitFixed solver (-x1)
  ret @?= lTrue

  ret <- SAT.getLitFixed solver x2
  ret @?= lTrue

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
  xs @?= [x3]

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
    xs <- QM.run $ SAT.getAssumptionsImplications solver
    forM_ xs $ \x -> do
      ret2 <- QM.run $ SAT.solveWith solver (-x : ls)
      QM.assert $ not ret2

------------------------------------------------------------------------

-- -4*(not x1) + 3*x1 + 10*(not x2)
-- = -4*(1 - x1) + 3*x1 + 10*(not x2)
-- = -4 + 4*x1 + 3*x1 + 10*(not x2)
-- = 7*x1 + 10*(not x2) - 4
case_normalizePBLinSum_1 :: Assertion
case_normalizePBLinSum_1 = do
  sort e @?= sort [(7,x1),(10,-x2)]
  c @?= -4
  where
    x1 = 1
    x2 = 2
    (e,c) = SAT.normalizePBLinSum ([(-4,-x1),(3,x1),(10,-x2)], 0)

prop_normalizePBLinSum :: Property
prop_normalizePBLinSum = forAll g $ \(nv, (s,n)) ->
    let (s2,n2) = SAT.normalizePBLinSum (s,n)
    in flip all (allAssignments nv) $ \m ->
         SAT.evalPBLinSum m s + n == SAT.evalPBLinSum m s2 + n2
  where
    g :: Gen (Int, (SAT.PBLinSum, Integer))
    g = do
      nv <- choose (0, 10)
      s <- forM [1..nv] $ \x -> do
        c <- arbitrary
        p <- arbitrary
        return (c, SAT.literal x p)
      n <- arbitrary
      return (nv, (s,n))

-- -4*(not x1) + 3*x1 + 10*(not x2) >= 3
-- ⇔ -4*(1 - x1) + 3*x1 + 10*(not x2) >= 3
-- ⇔ -4 + 4*x1 + 3*x1 + 10*(not x2) >= 3
-- ⇔ 7*x1 + 10*(not x2) >= 7
-- ⇔ 7*x1 + 7*(not x2) >= 7
-- ⇔ x1 + (not x2) >= 1
case_normalizePBLinAtLeast_1 :: Assertion
case_normalizePBLinAtLeast_1 = (sort lhs, rhs) @?= (sort [(1,x1),(1,-x2)], 1)
  where
    x1 = 1
    x2 = 2
    (lhs,rhs) = SAT.normalizePBLinAtLeast ([(-4,-x1),(3,x1),(10,-x2)], 3)

prop_normalizePBLinAtLeast :: Property
prop_normalizePBLinAtLeast = forAll g $ \(nv, c) ->
    let c2 = SAT.normalizePBLinAtLeast c
    in flip all (allAssignments nv) $ \m ->
         SAT.evalPBLinAtLeast m c == SAT.evalPBLinAtLeast m c2
  where
    g :: Gen (Int, SAT.PBLinAtLeast)
    g = do
      nv <- choose (0, 10)
      lhs <- forM [1..nv] $ \x -> do
        c <- arbitrary
        p <- arbitrary
        return (c, SAT.literal x p)
      rhs <- arbitrary
      return (nv, (lhs,rhs))

case_normalizePBLinExactly_1 :: Assertion
case_normalizePBLinExactly_1 = (sort lhs, rhs) @?= ([], 1)
  where
    x1 = 1
    x2 = 2
    (lhs,rhs) = SAT.normalizePBLinExactly ([(6,x1),(4,x2)], 2)

case_normalizePBLinExactly_2 :: Assertion
case_normalizePBLinExactly_2 = (sort lhs, rhs) @?= ([], 1)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    (lhs,rhs) = SAT.normalizePBLinExactly ([(2,x1),(2,x2),(2,x3)], 3)

prop_normalizePBLinExactly :: Property
prop_normalizePBLinExactly = forAll g $ \(nv, c) ->
    let c2 = SAT.normalizePBLinExactly c
    in flip all (allAssignments nv) $ \m ->
         SAT.evalPBLinExactly m c == SAT.evalPBLinExactly m c2
  where
    g :: Gen (Int, SAT.PBLinExactly)
    g = do
      nv <- choose (0, 10)
      lhs <- forM [1..nv] $ \x -> do
        c <- arbitrary
        p <- arbitrary
        return (c, SAT.literal x p)
      rhs <- arbitrary
      return (nv, (lhs,rhs))

prop_cutResolve :: Property
prop_cutResolve =
  forAll (choose (1, 10)) $ \nv ->
    forAll (g nv True) $ \c1 ->
      forAll (g nv False) $ \c2 ->
        let c3 = SAT.cutResolve c1 c2 1
        in flip all (allAssignments nv) $ \m ->
             not (SAT.evalPBLinExactly m c1 && SAT.evalPBLinExactly m c2) || SAT.evalPBLinExactly m c3
  where
    g :: Int -> Bool -> Gen SAT.PBLinExactly
    g nv b = do
      lhs <- forM [1..nv] $ \x -> do
        if x==1 then do
          c <- liftM ((1+) . abs) arbitrary
          return (c, SAT.literal x b)
        else do
          c <- arbitrary
          p <- arbitrary
          return (c, SAT.literal x p)
      rhs <- arbitrary
      return (lhs, rhs)

case_cutResolve_1 :: Assertion
case_cutResolve_1 = (sort lhs, rhs) @?= (sort [(1,x3),(1,x4)], 1)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    x4 = 4
    pb1 = ([(1,x1), (1,x2), (1,x3)], 1)
    pb2 = ([(2,-x1), (2,-x2), (1,x4)], 3)
    (lhs,rhs) = SAT.cutResolve pb1 pb2 x1

case_cutResolve_2 :: Assertion
case_cutResolve_2 = (sort lhs, rhs) @?= (sort lhs2, rhs2)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    x4 = 4
    pb1 = ([(3,x1), (2,-x2), (1,x3), (1,x4)], 3)
    pb2 = ([(1,-x3), (1,x4)], 1)
    (lhs,rhs) = SAT.cutResolve pb1 pb2 x3
    (lhs2,rhs2) = ([(2,x1),(1,-x2),(1,x4)],2) -- ([(3,x1),(2,-x2),(2,x4)], 3)

case_cardinalityReduction :: Assertion
case_cardinalityReduction = (sort lhs, rhs) @?= ([1,2,3,4,5],4)
  where
    (lhs, rhs) = SAT.cardinalityReduction ([(6,1),(5,2),(4,3),(3,4),(2,5),(1,6)], 17)

case_pbSubsume_clause :: Assertion
case_pbSubsume_clause = SAT.pbSubsume ([(1,1),(1,-3)],1) ([(1,1),(1,2),(1,-3),(1,4)],1) @?= True

case_pbSubsume_1 :: Assertion
case_pbSubsume_1 = SAT.pbSubsume ([(1,1),(1,2),(1,-3)],2) ([(1,1),(2,2),(1,-3),(1,4)],1) @?= True

case_pbSubsume_2 :: Assertion
case_pbSubsume_2 = SAT.pbSubsume ([(1,1),(1,2),(1,-3)],2) ([(1,1),(2,2),(1,-3),(1,4)],3) @?= False

prop_removeNegationFromPBSum :: Property
prop_removeNegationFromPBSum =
  forAll (choose (0,10)) $ \nv ->
    forAll (arbitraryPBSum nv) $ \s ->
      let s' = SAT.removeNegationFromPBSum s
       in counterexample (show s') $ 
            forAll (arbitraryAssignment nv) $ \m -> SAT.evalPBSum m s === SAT.evalPBSum m s'

------------------------------------------------------------------------

case_normalizeXORClause_False :: Assertion
case_normalizeXORClause_False =
  SAT.normalizeXORClause ([],True) @?= ([],True)

case_normalizeXORClause_True :: Assertion
case_normalizeXORClause_True =
  SAT.normalizeXORClause ([],False) @?= ([],False)

-- x ⊕ y ⊕ x = y
case_normalizeXORClause_case1 :: Assertion
case_normalizeXORClause_case1 =
  SAT.normalizeXORClause ([1,2,1],True) @?= ([2],True)

-- x ⊕ ¬x = x ⊕ x ⊕ 1 = 1
case_normalizeXORClause_case2 :: Assertion
case_normalizeXORClause_case2 =
  SAT.normalizeXORClause ([1,-1],True) @?= ([],False)

prop_normalizeXORClause :: Property
prop_normalizeXORClause = forAll g $ \(nv, c) ->
    let c2 = SAT.normalizeXORClause c
    in flip all (allAssignments nv) $ \m ->
         SAT.evalXORClause m c == SAT.evalXORClause m c2
  where
    g :: Gen (Int, SAT.XORClause)
    g = do
      nv <- choose (0, 10)
      len <- choose (0, nv)
      lhs <- replicateM len $ choose (-nv, nv) `suchThat` (/= 0)
      rhs <- arbitrary
      return (nv, (lhs,rhs))

case_evalXORClause_case1 :: Assertion
case_evalXORClause_case1 =
  SAT.evalXORClause (array (1,2) [(1,True),(2,True)] :: Array Int Bool) ([1,2], True) @?= False

case_evalXORClause_case2 :: Assertion
case_evalXORClause_case2 =
  SAT.evalXORClause (array (1,2) [(1,False),(2,True)] :: Array Int Bool) ([1,2], True) @?= True

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

findMUSAssumptions_case1 :: MUS.Method -> IO ()
findMUSAssumptions_case1 method = do
  solver <- SAT.newSolver
  [x1,x2,x3] <- SAT.newVars solver 3
  sels@[y1,y2,y3,y4,y5,y6] <- SAT.newVars solver 6
  SAT.addClause solver [-y1, x1]
  SAT.addClause solver [-y2, -x1]
  SAT.addClause solver [-y3, -x1, x2]
  SAT.addClause solver [-y4, -x2]
  SAT.addClause solver [-y5, -x1, x3]
  SAT.addClause solver [-y6, -x3]

  ret <- SAT.solveWith solver sels
  ret @?= False

  actual <- MUS.findMUSAssumptions solver def{ MUS.optMethod = method }
  let actual'  = IntSet.map (\x -> x-3) actual
      expected = map IntSet.fromList [[1, 2], [1, 3, 4], [1, 5, 6]]
  actual' `elem` expected @?= True

case_findMUSAssumptions_Deletion :: Assertion
case_findMUSAssumptions_Deletion = findMUSAssumptions_case1 MUS.Deletion

case_findMUSAssumptions_Insertion :: Assertion
case_findMUSAssumptions_Insertion = findMUSAssumptions_case1 MUS.Insertion

case_findMUSAssumptions_QuickXplain :: Assertion
case_findMUSAssumptions_QuickXplain = findMUSAssumptions_case1 MUS.QuickXplain

------------------------------------------------------------------------

{-
c http://sun.iwu.edu/~mliffito/publications/jar_liffiton_CAMUS.pdf
c φ= (x1) ∧ (¬x1) ∧ (¬x1∨x2) ∧ (¬x2) ∧ (¬x1∨x3) ∧ (¬x3)
c MUSes(φ) = {{C1, C2}, {C1, C3, C4}, {C1, C5, C6}}
c MCSes(φ) = {{C1}, {C2, C3, C5}, {C2, C3, C6}, {C2, C4, C5}, {C2, C4, C6}}
p cnf 3 6
1 0
-1 0
-1 2 0
-2 0
-1 3 0
-3 0
-}

allMUSAssumptions_case1 :: MUSEnum.Method -> IO ()
allMUSAssumptions_case1 method = do
  solver <- SAT.newSolver
  [x1,x2,x3] <- SAT.newVars solver 3
  sels@[y1,y2,y3,y4,y5,y6] <- SAT.newVars solver 6
  SAT.addClause solver [-y1, x1]
  SAT.addClause solver [-y2, -x1]
  SAT.addClause solver [-y3, -x1, x2]
  SAT.addClause solver [-y4, -x2]
  SAT.addClause solver [-y5, -x1, x3]
  SAT.addClause solver [-y6, -x3]
  (muses, mcses) <- MUSEnum.allMUSAssumptions solver sels def{ MUSEnum.optMethod = method }
  Set.fromList muses @?= Set.fromList (map (IntSet.fromList . map (+3)) [[1,2], [1,3,4], [1,5,6]])
  Set.fromList mcses @?= Set.fromList (map (IntSet.fromList . map (+3)) [[1], [2,3,5], [2,3,6], [2,4,5], [2,4,6]])

case_allMUSAssumptions_CAMUS :: Assertion
case_allMUSAssumptions_CAMUS = allMUSAssumptions_case1 MUSEnum.CAMUS

case_allMUSAssumptions_DAA :: Assertion
case_allMUSAssumptions_DAA = allMUSAssumptions_case1 MUSEnum.DAA

case_allMUSAssumptions_MARCO :: Assertion
case_allMUSAssumptions_MARCO = allMUSAssumptions_case1 MUSEnum.MARCO

case_allMUSAssumptions_GurvichKhachiyan1999 :: Assertion
case_allMUSAssumptions_GurvichKhachiyan1999 = allMUSAssumptions_case1 MUSEnum.GurvichKhachiyan1999

{-
Boosting a Complete Technique to Find MSS and MUS thanks to a Local Search Oracle
http://www.cril.univ-artois.fr/~piette/IJCAI07_HYCAM.pdf
Example 3.
C0  : (d)
C1  : (b ∨ c)
C2  : (a ∨ b)
C3  : (a ∨ ¬c)
C4  : (¬b ∨ ¬e)
C5  : (¬a ∨ ¬b)
C6  : (a ∨ e)
C7  : (¬a ∨ ¬e)
C8  : (b ∨ e)
C9  : (¬a ∨ b ∨ ¬c)
C10 : (¬a ∨ b ∨ ¬d)
C11 : (a ∨ ¬b ∨ c)
C12 : (a ∨ ¬b ∨ ¬d)
-}
allMUSAssumptions_case2 :: MUSEnum.Method -> IO ()
allMUSAssumptions_case2 method = do
  solver <- SAT.newSolver
  [a,b,c,d,e] <- SAT.newVars solver 5
  sels@[y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12] <- SAT.newVars solver 13
  SAT.addClause solver [-y0, d]
  SAT.addClause solver [-y1, b, c]
  SAT.addClause solver [-y2, a, b]
  SAT.addClause solver [-y3, a, -c]
  SAT.addClause solver [-y4, -b, -e]
  SAT.addClause solver [-y5, -a, -b]
  SAT.addClause solver [-y6, a, e]
  SAT.addClause solver [-y7, -a, -e]
  SAT.addClause solver [-y8, b, e]
  SAT.addClause solver [-y9, -a, b, -c]
  SAT.addClause solver [-y10, -a, b, -d]
  SAT.addClause solver [-y11, a, -b, c]
  SAT.addClause solver [-y12, a, -b, -d]

  -- Only three of the MUSes (marked with asterisks) are on the paper.
  let cores =
        [ [y0,y1,y2,y5,y9,y12]
        , [y0,y1,y3,y4,y5,y6,y10]
        , [y0,y1,y3,y5,y7,y8,y12]
        , [y0,y1,y3,y5,y9,y12]
        , [y0,y1,y3,y5,y10,y11]
        , [y0,y1,y3,y5,y10,y12]
        , [y0,y2,y3,y5,y10,y11]
        , [y0,y2,y4,y5,y6,y10]
        , [y0,y2,y5,y7,y8,y12]
        , [y0,y2,y5,y10,y12]   -- (*)
        , [y1,y2,y4,y5,y6,y9]
        , [y1,y3,y4,y5,y6,y7,y8]
        , [y1,y3,y4,y5,y6,y9]
        , [y1,y3,y5,y7,y8,y11]
        , [y1,y3,y5,y9,y11]    -- (*)
        , [y2,y3,y5,y7,y8,y11]
        , [y2,y4,y5,y6,y7,y8]  -- (*)
        ]

  let remove1 :: [a] -> [[a]]
      remove1 [] = []
      remove1 (x:xs) = xs : [x : ys | ys <- remove1 xs]
  forM_ cores $ \core -> do
    ret <- SAT.solveWith solver core
    assertBool (show core ++ " should be a core") (not ret)
    forM (remove1 core) $ \xs -> do
      ret <- SAT.solveWith solver xs
      assertBool (show core ++ " should be satisfiable") ret

  (actual,_) <- MUSEnum.allMUSAssumptions solver sels def{ MUSEnum.optMethod = method }
  let actual'   = Set.fromList actual
      expected' = Set.fromList $ map IntSet.fromList $ cores
  actual' @?= expected'

case_allMUSAssumptions_2_CAMUS :: Assertion
case_allMUSAssumptions_2_CAMUS = allMUSAssumptions_case2 MUSEnum.CAMUS

case_allMUSAssumptions_2_DAA :: Assertion
case_allMUSAssumptions_2_DAA = allMUSAssumptions_case2 MUSEnum.DAA

case_allMUSAssumptions_2_MARCO :: Assertion
case_allMUSAssumptions_2_MARCO = allMUSAssumptions_case2 MUSEnum.MARCO

case_allMUSAssumptions_2_GurvichKhachiyan1999 :: Assertion
case_allMUSAssumptions_2_GurvichKhachiyan1999 = allMUSAssumptions_case2 MUSEnum.GurvichKhachiyan1999

case_allMUSAssumptions_2_HYCAM :: Assertion
case_allMUSAssumptions_2_HYCAM = do
  solver <- SAT.newSolver
  [a,b,c,d,e] <- SAT.newVars solver 5
  sels@[y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12] <- SAT.newVars solver 13
  SAT.addClause solver [-y0, d]
  SAT.addClause solver [-y1, b, c]
  SAT.addClause solver [-y2, a, b]
  SAT.addClause solver [-y3, a, -c]
  SAT.addClause solver [-y4, -b, -e]
  SAT.addClause solver [-y5, -a, -b]
  SAT.addClause solver [-y6, a, e]
  SAT.addClause solver [-y7, -a, -e]
  SAT.addClause solver [-y8, b, e]
  SAT.addClause solver [-y9, -a, b, -c]
  SAT.addClause solver [-y10, -a, b, -d]
  SAT.addClause solver [-y11, a, -b, c]
  SAT.addClause solver [-y12, a, -b, -d]

  -- Only three of the MUSes (marked with asterisks) are on the paper.
  let cores =
        [ [y0,y1,y2,y5,y9,y12]
        , [y0,y1,y3,y4,y5,y6,y10]
        , [y0,y1,y3,y5,y7,y8,y12]
        , [y0,y1,y3,y5,y9,y12]
        , [y0,y1,y3,y5,y10,y11]
        , [y0,y1,y3,y5,y10,y12]
        , [y0,y2,y3,y5,y10,y11]
        , [y0,y2,y4,y5,y6,y10]
        , [y0,y2,y5,y7,y8,y12]
        , [y0,y2,y5,y10,y12]   -- (*)
        , [y1,y2,y4,y5,y6,y9]
        , [y1,y3,y4,y5,y6,y7,y8]
        , [y1,y3,y4,y5,y6,y9]
        , [y1,y3,y5,y7,y8,y11]
        , [y1,y3,y5,y9,y11]    -- (*)
        , [y2,y3,y5,y7,y8,y11]
        , [y2,y4,y5,y6,y7,y8]  -- (*)
        ]
      mcses =
        [ [y0,y1,y7]
        , [y0,y1,y8]
        , [y0,y3,y4]
        , [y0,y3,y6]
        , [y0,y4,y11]
        , [y0,y6,y11]
        , [y0,y7,y9]
        , [y0,y8,y9]
        , [y1,y2]
        , [y1,y7,y10]
        , [y1,y8,y10]
        , [y2,y3]
        , [y3,y4,y12]
        , [y3,y6,y12]
        , [y4,y11,y12]
        , [y5]
        , [y6,y11,y12]
        , [y7,y9,y10]
        , [y8,y9,y10]
        ]

  -- HYCAM paper wrongly treated {C3,C8,C10} as a candidate MCS (CoMSS).
  -- Its complement {C0,C1,C2,C4,C5,C6,C7,C9,C11,C12} is unsatisfiable
  -- and hence not MSS.
  ret <- SAT.solveWith solver [y0,y1,y2,y4,y5,y6,y7,y9,y11,y12]
  assertBool "failed to prove the bug of HYCAM paper" (not ret)
  
  let cand = map IntSet.fromList [[y5], [y3,y2], [y0,y1,y2]]
  (actual,_) <- MUSEnum.allMUSAssumptions solver sels def{ MUSEnum.optMethod = MUSEnum.CAMUS, MUSEnum.optKnownCSes = cand }
  let actual'   = Set.fromList $ actual
      expected' = Set.fromList $ map IntSet.fromList cores
  actual' @?= expected'

------------------------------------------------------------------------
-- Test harness

satTestGroup :: TestTree
satTestGroup = $(testGroupGenerator)
