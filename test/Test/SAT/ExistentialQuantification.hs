{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, FlexibleContexts #-}
module Test.SAT.ExistentialQuantification (satExistentialQuantificationTestGroup) where

import Control.Applicative
import Control.Monad
import qualified Data.IntSet as IntSet

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.ExistentialQuantification as ExistentialQuantification
import qualified ToySolver.FileFormat.CNF as CNF

import Test.SAT.Utils

prop_ExistentialQuantification :: Property
prop_ExistentialQuantification = QM.monadicIO $ do
  phi <- QM.pick arbitraryCNF
  xs <- QM.pick $ liftM IntSet.fromList $ sublistOf [1 .. CNF.cnfNumVars phi]
  let ys = IntSet.fromList [1 .. CNF.cnfNumVars phi] IntSet.\\ xs
  psi <- QM.run $ ExistentialQuantification.project xs phi
  forM_ (allAssignments (if IntSet.null ys then 0 else IntSet.findMax ys)) $ \m -> do
    b1 <- QM.run $ do
      solver <- SAT.newSolver
      SAT.newVars_ solver (CNF.cnfNumVars phi)
      forM_ (CNF.cnfClauses phi) $ \c -> SAT.addClause solver (SAT.unpackClause c)
      SAT.solveWith solver [if SAT.evalLit m y then y else -y | y <- IntSet.toList ys]
    let b2 = evalCNF m psi
    QM.assert $ b1 == b2

brauer11_phi :: CNF.CNF
brauer11_phi =
  CNF.CNF
  { CNF.cnfNumVars = 13
  , CNF.cnfNumClauses = 23
  , CNF.cnfClauses = fmap SAT.packClause
      [
      -- μ
        [-x2, -y2]
      , [-y2, -y1]
      , [-x4, -x6, y1]
      , [-x3, y4], [x3, -y4]
      , [-x4, y3], [x4, -y3]
      , [-x5, y6], [x5, -y6]
      , [-x6, y5], [x6, -y5]

      -- ξ
      , [-x13, x1]
      , [-x13, -x2]
      , [-x13, x3]
      , [-x13, -x4]
      , [-x13, x5]
      , [-x13, -x6]
      , [x13, x1]
      , [x13, -x2]
      , [x13, -x3]
      , [x13, x4]
      , [x13, -x5]
      , [x13, x6]
      ]
  }
  where
    [y1,y2,y3,y4,y5,y6] = [1..6]
    [x1,x2,x3,x4,x5,x6,x13] = [7..13]

{-
ξ(m'1) = (¬y1 ∧ ¬y3 ∧ y4 ∧ ¬y5 ∧ y6)
ξ(m'2) = (y1 ∧ ¬y2 ∧ ¬y3 ∧ y4 ∧ ¬y5 ∧ y6)
ξ(m'3) = (y1 ∧ ¬y2 ∧ y3 ∧ ¬y4 ∧ y5 ∧ ¬y6)
ω = ¬(ξ(m'1) ∨ ξ(m'2) ∨ ξ(m'3))
-}
brauer11_omega :: CNF.CNF
brauer11_omega =
  CNF.CNF
  { CNF.cnfNumVars = 6
  , CNF.cnfNumClauses = 3
  , CNF.cnfClauses = map SAT.packClause
      [ [y1, y3, -y4, y5, -y6]
      , [-y1, y2, y3, -y4, y5, -y6]
      , [-y1, y2, -y3, y4, -y5, y6]
      ]
  }
  where
    [y1,y2,y3,y4,y5,y6] = [1..6]

case_ExistentialQuantification_project_phi :: Assertion
case_ExistentialQuantification_project_phi = do
  psi <- ExistentialQuantification.project (IntSet.fromList [7..13]) brauer11_phi
  forM_ (allAssignments 6) $ \m -> do
    b1 <- do
      solver <- SAT.newSolver
      SAT.newVars_ solver (CNF.cnfNumVars brauer11_phi)
      forM_ (CNF.cnfClauses brauer11_phi) $ \c -> SAT.addClause solver (SAT.unpackClause c)
      SAT.solveWith solver [if SAT.evalLit m y then y else -y | y <- [1..6]]
    let b2 = all (SAT.evalClause m . SAT.unpackClause) (CNF.cnfClauses psi)
    (b1 == b2) @?= True

case_ExistentialQuantification_project_phi' :: Assertion
case_ExistentialQuantification_project_phi' = do
  let [y1,y2,y3,y4,y5,y6] = [1..6]
      psi = CNF.CNF
            { CNF.cnfNumVars = 6
            , CNF.cnfNumClauses = 8
            , CNF.cnfClauses = map SAT.packClause
                [ [-y2, y6]
                , [-y3, -y6]
                , [y5, y6]
                , [y3, -y5]
                , [y4, -y6]
                , [y1, y6]
                , [-y1, -y2]
                , [-y4, y6]
                ]
            }
  forM_ (allAssignments 6) $ \m -> do
    b1 <- do
      solver <- SAT.newSolver
      SAT.newVars_ solver (CNF.cnfNumVars brauer11_phi)
      forM_ (CNF.cnfClauses brauer11_phi) $ \c -> SAT.addClause solver (SAT.unpackClause c)
      SAT.solveWith solver [if SAT.evalLit m y then y else -y | y <- [1..6]]
    let b2 = all (SAT.evalClause m . SAT.unpackClause) (CNF.cnfClauses psi)    
    (b1 == b2) @?= True

case_shortestImplicantsE_phi :: Assertion
case_shortestImplicantsE_phi = do
  xss <- ExistentialQuantification.shortestImplicantsE (IntSet.fromList [7..13]) brauer11_phi
  forM_ (allAssignments 6) $ \m -> do
    b1 <- do
      solver <- SAT.newSolver
      SAT.newVars_ solver (CNF.cnfNumVars brauer11_phi)
      forM_ (CNF.cnfClauses brauer11_phi) $ \c -> SAT.addClause solver (SAT.unpackClause c)
      SAT.solveWith solver [if SAT.evalLit m y then y else -y | y <- [1..6]]
    let b2 = any (all (SAT.evalLit m) . IntSet.toList) xss
    (b1 == b2) @?= True

case_shortestImplicantsE_phi' :: Assertion
case_shortestImplicantsE_phi' = do
  let [y1,y2,y3,y4,y5,y6] = [1..6]
      xss = map IntSet.fromList
            [ [-y1, -y3, y4, -y5, y6]
            , [y1, -y2, -y3, y4, -y5, y6]
            , [y1, -y2, y3, -y4, y5, -y6]
            ]
  forM_ (allAssignments 6) $ \m -> do
    b1 <- do
      solver <- SAT.newSolver
      SAT.newVars_ solver (CNF.cnfNumVars brauer11_phi)
      forM_ (CNF.cnfClauses brauer11_phi) $ \c -> SAT.addClause solver (SAT.unpackClause c)
      SAT.solveWith solver [if SAT.evalLit m y then y else -y | y <- [1..6]]
    let b2 = any (all (SAT.evalLit m) . IntSet.toList) xss
    (b1 == b2) @?= True

case_shortestImplicantsE_omega :: Assertion
case_shortestImplicantsE_omega = do
  xss <- ExistentialQuantification.shortestImplicantsE IntSet.empty brauer11_omega
  forM_ (allAssignments 6) $ \m -> do
    b1 <- do
      solver <- SAT.newSolver
      SAT.newVars_ solver (CNF.cnfNumVars brauer11_omega)
      forM_ (CNF.cnfClauses brauer11_omega) $ \c -> SAT.addClause solver (SAT.unpackClause c)
      SAT.solveWith solver [if SAT.evalLit m y then y else -y | y <- [1..6]]
    let b2 = any (all (SAT.evalLit m) . IntSet.toList) xss
    unless (b1 == b2) $ print m

case_shortestImplicantsE_omega' :: Assertion
case_shortestImplicantsE_omega' = do
  let [y1,y2,y3,y4,y5,y6] = [1..6]
      xss = map IntSet.fromList
              [ [y2, -y6]
              , [y3, y6]
              , [-y5, -y6]
              , [-y3, y5]
              , [-y4, y6]
              , [-y1, -y6]
              , [y1, y2]
              , [y4, -y6]
              ]
  forM_ (allAssignments 6) $ \m -> do
    b1 <- do
      solver <- SAT.newSolver
      SAT.newVars_ solver (CNF.cnfNumVars brauer11_omega)
      forM_ (CNF.cnfClauses brauer11_omega) $ \c -> SAT.addClause solver (SAT.unpackClause c)
      SAT.solveWith solver [if SAT.evalLit m y then y else -y | y <- [1..6]]
    let b2 = any (all (SAT.evalLit m) . IntSet.toList) xss
    (b1 == b2) @?= True

prop_negateCNF :: Property
prop_negateCNF = QM.monadicIO $ do
  phi <- QM.pick arbitraryCNF
  psi <- QM.run $ ExistentialQuantification.negateCNF phi
  QM.monitor (counterexample $ show psi)
  forM_ (allAssignments (CNF.cnfNumVars phi)) $ \m -> do
    let b1 = evalCNF m phi
        b2 = evalCNF m psi
    unless (b1 /= b2) $ QM.monitor (counterexample $ show m)
    QM.assert $ b1 /= b2

satExistentialQuantificationTestGroup :: TestTree
satExistentialQuantificationTestGroup = $(testGroupGenerator)
