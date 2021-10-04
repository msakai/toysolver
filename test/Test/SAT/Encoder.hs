{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.SAT.Encoder (satEncoderTestGroup) where

import Control.Monad
import Data.Array.IArray
import Data.List
import Data.Maybe
import qualified Data.Vector as V

import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import ToySolver.Data.BoolExpr
import ToySolver.Data.Boolean
import ToySolver.Data.LBool
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.Encoder.Cardinality as Cardinality
import qualified ToySolver.SAT.Encoder.Cardinality.Internal.Totalizer as Totalizer
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

prop_CardinalityEncoder_addAtLeast :: Property
prop_CardinalityEncoder_addAtLeast = QM.monadicIO $ do
  let nv = 4
  (lhs,rhs) <- QM.pick $ do
    lhs <- liftM catMaybes $ forM [1..nv] $ \i -> do
      b <- arbitrary
      if b then
        Just <$> elements [i, -i]
      else
        return Nothing
    rhs <- choose (-1, nv+2)
    return $ (lhs, rhs)
  strategy <- QM.pick arbitrary
  (cnf,defs,defs2) <- QM.run $ do
    db <- CNFStore.newCNFStore
    SAT.newVars_ db nv
    tseitin <- Tseitin.newEncoder db
    card <- Cardinality.newEncoderWithStrategy tseitin strategy
    SAT.addAtLeast card lhs rhs
    cnf <- CNFStore.getCNFFormula db
    defs <- Tseitin.getDefinitions tseitin
    defs2 <- Cardinality.getTotalizerDefinitions card
    return (cnf, defs, defs2)
  forM_ (allAssignments nv) $ \m -> do
    let m2 :: Array SAT.Var Bool
        m2 = array (1, CNF.cnfNumVars cnf) $
               assocs m ++
               [(v, Tseitin.evalFormula m2 phi) | (v,phi) <- defs] ++
               Cardinality.evalTotalizerDefinitions m2 defs2
        b1 = SAT.evalAtLeast m (lhs,rhs)
        b2 = evalCNF (array (bounds m2) (assocs m2)) cnf
    QM.assert $ b1 == b2


case_Totalizer_unary :: Assertion
case_Totalizer_unary = do
  solver <- SAT.newSolver
  tseitin <- Tseitin.newEncoder solver
  totalizer <- Totalizer.newEncoder tseitin
  SAT.newVars_ solver 5
  xs <- Totalizer.encodeSum totalizer [1,2,3,4,5]
  SAT.addClause solver [xs !! 2]
  SAT.addClause solver [- (xs !! 1)]
  ret <- SAT.solve solver
  ret @?= False


-- -- This does not hold:
-- case_Totalizer_pre_unary :: Assertion
-- case_Totalizer_pre_unary = do
--   solver <- SAT.newSolver
--   tseitin <- Tseitin.newEncoder solver
--   totalizer <- Totalizer.newEncoder tseitin
--   SAT.newVars_ solver 5
--   xs <- Totalizer.encodeSum totalizer [1,2,3,4,5]
--   SAT.addClause solver [xs !! 2]
--   v0 <- SAT.getLitFixed solver (xs !! 0)
--   v1 <- SAT.getLitFixed solver (xs !! 1)
--   v0 @?= lTrue
--   v1 @?= lTrue


prop_Totalizer_forward_propagation :: Property
prop_Totalizer_forward_propagation = QM.monadicIO $ do
  nv <- QM.pick $ choose (2, 10) -- inclusive range
  let xs = [1..nv]
  (xs1, xs2) <- QM.pick $ do
    cs <- forM xs $ \x -> do
      c <- arbitrary
      return (x,c)
    return ([x | (x, Just True) <- cs], [x | (x, Just False) <- cs])
  let p = length xs1
      q = length xs2
  lbs <- QM.run $ do
    solver <- SAT.newSolver
    tseitin <- Tseitin.newEncoder solver
    totalizer <- Totalizer.newEncoder tseitin
    SAT.newVars_ solver nv
    ys <- Totalizer.encodeSum totalizer xs
    forM_ xs1 $ \x -> SAT.addClause solver [x]
    forM_ xs2 $ \x -> SAT.addClause solver [-x]
    forM ys $ SAT.getLitFixed solver
  QM.monitor $ counterexample (show lbs)
  QM.assert $ lbs == replicate p lTrue ++ replicate (nv - p - q) lUndef ++ replicate q lFalse


prop_Totalizer_backward_propagation :: Property
prop_Totalizer_backward_propagation = QM.monadicIO $ do
  nv <- QM.pick $ choose (2, 10) -- inclusive range
  let xs = [1..nv]
  (xs1, xs2) <- QM.pick $ do
    cs <- forM xs $ \x -> do
      c <- arbitrary
      return (x,c)
    return ([x | (x, Just True) <- cs], [x | (x, Just False) <- cs])
  let p = length xs1
      q = length xs2
  e <- QM.pick arbitrary
  lbs <- QM.run $ do
    solver <- SAT.newSolver
    tseitin <- Tseitin.newEncoder solver
    totalizer <- Totalizer.newEncoder tseitin
    SAT.newVars_ solver nv
    ys <- Totalizer.encodeSum totalizer xs
    forM_ xs1 $ \x -> SAT.addClause solver [x]
    forM_ xs2 $ \x -> SAT.addClause solver [-x]
    forM_ (take (nv - p - q) (drop p ys)) $ \x -> do
      SAT.addClause solver [if e then x else - x]
    forM xs $ SAT.getLitFixed solver
  QM.monitor $ counterexample (show lbs)
  QM.assert $ and [x `elem` xs1 || x `elem` xs2 || lbs !! (x-1) == liftBool e | x <- xs]


prop_encodeAtLeast :: Property
prop_encodeAtLeast = QM.monadicIO $ do
  let nv = 4
  (lhs,rhs) <- QM.pick $ do
    lhs <- liftM catMaybes $ forM [1..nv] $ \i -> do
      b <- arbitrary
      if b then
        Just <$> elements [i, -i]
      else
        return Nothing
    rhs <- choose (-1, nv+2)
    return $ (lhs, rhs)
  strategy <- QM.pick arbitrary
  (l,cnf,defs,defs2) <- QM.run $ do
    db <- CNFStore.newCNFStore
    SAT.newVars_ db nv
    tseitin <- Tseitin.newEncoder db
    card <- Cardinality.newEncoderWithStrategy tseitin strategy
    l <- Cardinality.encodeAtLeast card (lhs, rhs)
    cnf <- CNFStore.getCNFFormula db
    defs <- Tseitin.getDefinitions tseitin
    defs2 <- Cardinality.getTotalizerDefinitions card
    return (l, cnf, defs, defs2)
  forM_ (allAssignments nv) $ \m -> do
    let m2 :: Array SAT.Var Bool
        m2 = array (1, CNF.cnfNumVars cnf) $
               assocs m ++
               [(v, Tseitin.evalFormula m2 phi) | (v,phi) <- defs] ++
               Cardinality.evalTotalizerDefinitions m2 defs2
        b1 = evalCNF (array (bounds m2) (assocs m2)) cnf
    QM.assert $ not b1 || (SAT.evalLit m2 l == SAT.evalAtLeast m (lhs,rhs))


satEncoderTestGroup :: TestTree
satEncoderTestGroup = $(testGroupGenerator)
