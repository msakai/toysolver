{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.SAT.MUS (satMUSTestGroup) where

import Control.Monad
import Data.Default.Class
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.MUS as MUS
import qualified ToySolver.SAT.MUS.Enum as MUSEnum

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

satMUSTestGroup :: TestTree
satMUSTestGroup = $(testGroupGenerator)
