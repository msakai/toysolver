{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, FlexibleContexts #-}
module Test.SAT.Encoder (satEncoderTestGroup) where

import Control.Monad
import Data.Array.IArray
import Data.List
import qualified Data.Vector as V

import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import ToySolver.Data.BoolExpr
import ToySolver.Data.Boolean
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.Encoder.PB as PB
import qualified ToySolver.SAT.Encoder.PB.Internal.Sorter as PBEncSorter
import qualified ToySolver.SAT.Store.CNF as CNFStore

import Test.SAT.Utils

case_addFormula :: Assertion
case_addFormula = do
  solver <- SAT.newSolver
  enc <- Tseitin.newEncoder solver

  [x1,x2,x3,x4,x5] <- replicateM 5 $ liftM Atom $ SAT.newVar solver
  Tseitin.addFormula enc $ orB [x1 .=>. x3 .&&. x4, x2 .=>. x3 .&&. x5]
  -- x6 = x3 ∧ x4
  -- x7 = x3 ∧ x5
  Tseitin.addFormula enc $ x1 .||. x2
  Tseitin.addFormula enc $ x4 .=>. notB x5
  ret <- SAT.solve solver
  ret @?= True

  Tseitin.addFormula enc $ x2 .<=>. x4
  ret <- SAT.solve solver
  ret @?= True

  Tseitin.addFormula enc $ x1 .<=>. x5
  ret <- SAT.solve solver
  ret @?= True

  Tseitin.addFormula enc $ notB x1 .=>. x3 .&&. x5
  ret <- SAT.solve solver
  ret @?= True

  Tseitin.addFormula enc $ notB x2 .=>. x3 .&&. x4
  ret <- SAT.solve solver
  ret @?= False

case_addFormula_Peirces_Law :: Assertion
case_addFormula_Peirces_Law = do
  solver <- SAT.newSolver
  enc <- Tseitin.newEncoder solver
  [x1,x2] <- replicateM 2 $ liftM Atom $ SAT.newVar solver
  Tseitin.addFormula enc $ notB $ ((x1 .=>. x2) .=>. x1) .=>. x1
  ret <- SAT.solve solver
  ret @?= False

case_encodeConj :: Assertion
case_encodeConj = do
  solver <- SAT.newSolver
  enc <- Tseitin.newEncoder solver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- Tseitin.encodeConj enc [x1,x2]

  ret <- SAT.solveWith solver [x3]
  ret @?= True
  m <- SAT.getModel solver
  SAT.evalLit m x1 @?= True
  SAT.evalLit m x2 @?= True
  SAT.evalLit m x3 @?= True

  ret <- SAT.solveWith solver [-x3]
  ret @?= True
  m <- SAT.getModel solver
  (SAT.evalLit m x1 && SAT.evalLit m x2) @?= False
  SAT.evalLit m x3 @?= False

case_encodeDisj :: Assertion
case_encodeDisj = do
  solver <- SAT.newSolver
  enc <- Tseitin.newEncoder solver
  x1 <- SAT.newVar solver
  x2 <- SAT.newVar solver
  x3 <- Tseitin.encodeDisj enc [x1,x2]

  ret <- SAT.solveWith solver [x3]
  ret @?= True
  m <- SAT.getModel solver
  (SAT.evalLit m x1 || SAT.evalLit m x2) @?= True
  SAT.evalLit m x3 @?= True

  ret <- SAT.solveWith solver [-x3]
  ret @?= True
  m <- SAT.getModel solver
  SAT.evalLit m x1 @?= False
  SAT.evalLit m x2 @?= False
  SAT.evalLit m x3 @?= False

case_evalFormula :: Assertion
case_evalFormula = do
  solver <- SAT.newSolver
  xs <- SAT.newVars solver 5
  let f = (x1 .=>. x3 .&&. x4) .||. (x2 .=>. x3 .&&. x5)
        where
          [x1,x2,x3,x4,x5] = map Atom xs
      g :: SAT.Model -> Bool
      g m = (not x1 || (x3 && x4)) || (not x2 || (x3 && x5))
        where
          [x1,x2,x3,x4,x5] = elems m
  forM_ (allAssignments 5) $ \m -> do
    Tseitin.evalFormula m f @?= g m

prop_PBEncoder_addPBAtLeast :: Property
prop_PBEncoder_addPBAtLeast = QM.monadicIO $ do
  let nv = 4
  (lhs,rhs) <- QM.pick $ do
    lhs <- arbitraryPBLinSum nv
    rhs <- arbitrary
    return $ SAT.normalizePBLinAtLeast (lhs, rhs)
  strategy <- QM.pick arbitrary
  (cnf,defs) <- QM.run $ do
    db <- CNFStore.newCNFStore
    SAT.newVars_ db nv
    tseitin <- Tseitin.newEncoder db
    pb <- PB.newEncoderWithStrategy tseitin strategy
    SAT.addPBAtLeast pb lhs rhs
    cnf <- CNFStore.getCNFFormula db
    defs <- Tseitin.getDefinitions tseitin
    return (cnf, defs)
  forM_ (allAssignments 4) $ \m -> do
    let m2 :: Array SAT.Var Bool
        m2 = array (1, CNF.cnfNumVars cnf) $ assocs m ++ [(v, Tseitin.evalFormula m2 phi) | (v,phi) <- defs]
        b1 = SAT.evalPBLinAtLeast m (lhs,rhs)
        b2 = evalCNF (array (bounds m2) (assocs m2)) cnf
    QM.assert $ b1 == b2

prop_PBEncoder_Sorter_genSorter :: [Int] -> Bool
prop_PBEncoder_Sorter_genSorter xs =
  V.toList (PBEncSorter.sortVector (V.fromList xs)) == sort xs

prop_PBEncoder_Sorter_decode_encode :: Property
prop_PBEncoder_Sorter_decode_encode =
  forAll arbitrary $ \base' ->
    forAll arbitrary $ \(NonNegative x) ->
      let base = [b | Positive b <- base']
      in PBEncSorter.isRepresentable base x
         ==>
         (PBEncSorter.decode base . PBEncSorter.encode base) x == x


satEncoderTestGroup :: TestTree
satEncoderTestGroup = $(testGroupGenerator)
