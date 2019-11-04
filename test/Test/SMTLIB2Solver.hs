{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.SMTLIB2Solver (smtlib2SolverTestGroup) where

import Control.Applicative((<$>))
import Control.Exception (evaluate)
import Control.Monad
import Control.Monad.State.Strict
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import ToySolver.SMT.SMTLIB2Solver as SMTLIB2

case_assertionStackLevels :: Assertion
case_assertionStackLevels = do
  solver <- SMTLIB2.newSolver
  SMTLIB2.setLogic solver "QF_UF"
  lv1 <- SMTLIB2.getInfo solver AssertionStackLevels
  lv1 @?= [ResponseAssertionStackLevels 0]
  SMTLIB2.push solver 1
  lv2 <- SMTLIB2.getInfo solver AssertionStackLevels
  lv2 @?= [ResponseAssertionStackLevels 1]
  SMTLIB2.pop solver 1
  lv3 <- SMTLIB2.getInfo solver AssertionStackLevels
  lv3 @?= [ResponseAssertionStackLevels 0]

case_getUnsatAssumptions :: Assertion
case_getUnsatAssumptions = do
  solver <- SMTLIB2.newSolver
  SMTLIB2.setOption solver (ProduceUnsatAssumptions True)
  o <- SMTLIB2.getOption solver ":produce-unsat-assumptions"
  o @?= AttrValueSymbol "true"
  SMTLIB2.setLogic solver "QF_UF"
  SMTLIB2.declareFun solver "a" [] (SortId (ISymbol "Bool"))
  SMTLIB2.declareFun solver "b" [] (SortId (ISymbol "Bool"))
  SMTLIB2.runCommandString solver "(assert (or a b))"
  r <- SMTLIB2.runCommandString solver "(check-sat-assuming ((not a) (not b)))"
  r @?= CmdCheckSatResponse Unsat
  r <- SMTLIB2.getUnsatAssumptions solver
  let expected =
       [ TermQualIdentifierT (QIdentifier (ISymbol "not")) [TermQualIdentifier (QIdentifier (ISymbol "a"))]
       , TermQualIdentifierT (QIdentifier (ISymbol "not")) [TermQualIdentifier (QIdentifier (ISymbol "b"))]
       ]
  r @?= expected

case_declareConst :: Assertion
case_declareConst = do
  solver <- SMTLIB2.newSolver
  SMTLIB2.setLogic solver "QF_LRA"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-const b Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-const x Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-const y Bool)"

case_divisionByZero :: Assertion
case_divisionByZero = do
  solver <- SMTLIB2.newSolver
  SMTLIB2.setOption solver (ProduceUnsatAssumptions True)
  SMTLIB2.setLogic solver "QF_LRA"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-const x1 Real)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-const x2 Real)"

  assertSuccess =<< SMTLIB2.runCommandString solver "(define-fun y1 () Real (/ x1 0))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(define-fun y2 () Real (/ x2 0))"
  r <- SMTLIB2.checkSat solver
  r @?= Sat

  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (not (= y1 y2)))"
  r <- SMTLIB2.checkSat solver
  r @?= Sat

  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (= x1 x2))"
  r <- SMTLIB2.checkSat solver
  r @?= Unsat

case_getAssertions :: Assertion
case_getAssertions = do
  solver <- SMTLIB2.newSolver
  SMTLIB2.setOption solver (ProduceAssertions True)
  o <- SMTLIB2.getOption solver ":produce-assertions"
  o @?= AttrValueSymbol "true"
  SMTLIB2.setLogic solver "QF_UF"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun a () Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun b () Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (or (! a :named aa) (! b :named bb)))"
  r <- SMTLIB2.runCommandString solver "(get-assertions)"
  showSL r @?= "((or (! a :named aa) (! b :named bb)))"
  SMTLIB2.push solver 1
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (not (and a bb)))"
  r <- SMTLIB2.runCommandString solver "(get-assertions)"
  showSL r @?= "((or (! a :named aa) (! b :named bb)) (not (and a bb)))"
  SMTLIB2.pop solver 1
  r <- SMTLIB2.runCommandString solver "(get-assertions)"
  showSL r @?= "((or (! a :named aa) (! b :named bb)))"

case_getAssignment :: Assertion
case_getAssignment = do
  solver <- SMTLIB2.newSolver
  SMTLIB2.setOption solver (ProduceAssignments True)
  o <- SMTLIB2.getOption solver ":produce-assignments"
  o @?= AttrValueSymbol "true"
  SMTLIB2.setLogic solver "QF_UFLRA"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun a () Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun b () Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun c () Real)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (or (! a :named aa) (! b :named bb)))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (>= (! c :named cc) 0))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (not (and a bb)))"
  SMTLIB2.checkSat solver
  r <- SMTLIB2.getAssignment solver
  let m = Map.fromList [(s, b) | TValuationPair s b <- r]
  unless (m == Map.fromList [("aa",True), ("bb",False)] || m == Map.fromList [("aa",False), ("bb",True)]) $ do
    assertFailure (show r)

case_getModel :: Assertion
case_getModel = do
  solver <- SMTLIB2.newSolver
  SMTLIB2.setOption solver (ProduceModels True)
  o <- SMTLIB2.getOption solver ":produce-models"
  o @?= AttrValueSymbol "true"
  SMTLIB2.setLogic solver "QF_UF"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun a () Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun b () Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (or a b))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (not (and a b)))"
  SMTLIB2.checkSat solver
  r <- SMTLIB2.getModel solver
  let m = sort $ map showSL r
  unless (m == ["(define-fun a () Bool true)", "(define-fun b () Bool false)"] ||
          m == ["(define-fun a () Bool false)", "(define-fun b () Bool true)"]) $ do
    assertFailure (show r)

case_getValue :: Assertion
case_getValue = do
  solver <- SMTLIB2.newSolver
  SMTLIB2.setOption solver (ProduceModels True)
  o <- SMTLIB2.getOption solver ":produce-models"
  o @?= AttrValueSymbol "true"
  SMTLIB2.setLogic solver "QF_UF"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-sort U 0)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun f (U) U)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun g (U) U)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun A () Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun x () U)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun y () U)"
  SMTLIB2.checkSat solver
  r <- SMTLIB2.runCommandString solver "(get-value (x A (f x) (g y)))"
  case r of
    CmdGetValueResponse xs -> return () -- fixme
    _ -> assertFailure (show r)

case_GlobalDeclarations :: Assertion
case_GlobalDeclarations = do
  solver <- SMTLIB2.newSolver

  SMTLIB2.setOption solver (GlobalDeclarations False)
  o <- SMTLIB2.getOption solver ":global-declarations"
  o @?= AttrValueSymbol "false"
  SMTLIB2.setLogic solver "QF_UFLRA"
  SMTLIB2.push solver 1
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-const x1 Bool)"
  SMTLIB2.pop solver 1
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-const x1 Real)"

  SMTLIB2.reset solver

  SMTLIB2.setOption solver (GlobalDeclarations True)
  o <- SMTLIB2.getOption solver ":global-declarations"
  o @?= AttrValueSymbol "true"
  SMTLIB2.setLogic solver "QF_UFLRA"
  SMTLIB2.push solver 1
  assertSuccess =<< SMTLIB2.runCommandString solver "(define-fun x2 () Real 1.0)"
  SMTLIB2.pop solver 1
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (= x2 1.0))"
  SMTLIB2.checkSat solver

  return ()

case_quoted_symbols :: Assertion
case_quoted_symbols = do
  solver <- SMTLIB2.newSolver
  SMTLIB2.setLogic solver "QF_LRA"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun abc () Real)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (= abc 0))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (= |abc| 1))"
  r <- SMTLIB2.checkSat solver
  r @?= Unsat

case_reset :: Assertion
case_reset = do
  solver <- SMTLIB2.newSolver

  SMTLIB2.setLogic solver "QF_UF"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun x1 () Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun x2 () Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun x3 () Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! x1 :named C1))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! (not x1) :named C2))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! (or (not x1) x2) :named C3))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! (not x2) :named C4))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! (or (not x1) x3) :named C5))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! (not x3) :named C6))"

  r <- SMTLIB2.checkSat solver
  r @?= Unsat

  SMTLIB2.reset solver

  r <- SMTLIB2.checkSat solver
  r @?= Sat

case_resetAssertions :: Assertion
case_resetAssertions = do
  solver <- SMTLIB2.newSolver

  SMTLIB2.setLogic solver "QF_UF"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun x1 () Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun x2 () Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun x3 () Bool)"
  SMTLIB2.push solver 1
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! x1 :named C1))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! (not x1) :named C2))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! (or (not x1) x2) :named C3))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! (not x2) :named C4))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! (or (not x1) x3) :named C5))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! (not x3) :named C6))"

  r <- SMTLIB2.checkSat solver
  r @?= Unsat

  SMTLIB2.resetAssertions solver

  r <- SMTLIB2.checkSat solver
  r @?= Sat

-- http://sun.iwu.edu/~mliffito/publications/jar_liffiton_CAMUS.pdf
-- φ= (x1) ∧ (¬x1) ∧ (¬x1∨x2) ∧ (¬x2) ∧ (¬x1∨x3) ∧ (¬x3)
-- MUSes(φ) = {{C1, C2}, {C1, C3, C4}, {C1, C5, C6}}
-- MCSes(φ) = {{C1}, {C2, C3, C5}, {C2, C3, C6}, {C2, C4, C5}, {C2, C4, C6}}
case_getUnsatCore :: Assertion
case_getUnsatCore = do
  solver <- SMTLIB2.newSolver

  SMTLIB2.setOption solver (ProduceUnsatCores True)
  o <- SMTLIB2.getOption solver ":produce-unsat-cores"
  o @?= AttrValueSymbol "true"

  SMTLIB2.setLogic solver "QF_UF"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun x1 () Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun x2 () Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-fun x3 () Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! x1 :named C1))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! (not x1) :named C2))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! (or (not x1) x2) :named C3))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! (not x2) :named C4))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! (or (not x1) x3) :named C5))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (! (not x3) :named C6))"
  r <- SMTLIB2.checkSat solver
  r @?= Unsat
  r <- SMTLIB2.getUnsatCore solver
  let expected = map Set.fromList [["C1", "C2"], ["C1", "C3", "C4"], ["C1", "C5", "C6"]]
  Set.fromList r `elem` expected @?= True

case_echo :: Assertion
case_echo = do
  solver <- SMTLIB2.newSolver
  r <- SMTLIB2.runCommandString solver "(echo \"hello\")"
  showSL r @?= "\"hello\""

case_let :: Assertion
case_let = do
  solver <- SMTLIB2.newSolver
  SMTLIB2.setLogic solver "QF_LRA"
  assertSuccess =<< SMTLIB2.runCommandString solver "(define-fun x () Real (let ((y 1)) (+ y 2)))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (not (= x 3)))"
  r <- SMTLIB2.checkSat solver
  r @?= Unsat

case_delcareSort :: Assertion
case_delcareSort = do
  solver <- SMTLIB2.newSolver
  SMTLIB2.setLogic solver "QF_UFLRA"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-sort U 1)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-const x1 (U Real))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-const x2 (U Bool))"

case_defineSort :: Assertion
case_defineSort = do
  solver <- SMTLIB2.newSolver
  SMTLIB2.setLogic solver "QF_UFLRA"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-sort U 1)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(define-sort T (X) (U X))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-const x1 (T Real))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-const x2 (T Bool))"

case_defineFun :: Assertion
case_defineFun = do
  solver <- SMTLIB2.newSolver
  SMTLIB2.setOption solver (ProduceModels True)
  SMTLIB2.setLogic solver "QF_UFLRA"
  assertSuccess =<< SMTLIB2.runCommandString solver "(define-fun f ((b Bool) (x Real)) Bool (ite b (>= x 0) (>= 0 x)))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-const bb Bool)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(declare-const xx Real)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (>= xx 100))"
  assertSuccess =<< SMTLIB2.runCommandString solver "(assert (f bb xx))"
  r <- SMTLIB2.checkSat solver
  r @?= Sat
  r <- SMTLIB2.runCommandString solver "(get-value (bb))"
  showSL r @?= "((bb true))"

case_getInfo :: Assertion
case_getInfo = do
  solver <- SMTLIB2.newSolver
  _ <- SMTLIB2.getInfo solver ErrorBehavior
  _ <- SMTLIB2.getInfo solver Name
  _ <- SMTLIB2.getInfo solver Authors
  _ <- SMTLIB2.getInfo solver Version
  return ()

case_setInfo :: Assertion
case_setInfo = do
  solver <- SMTLIB2.newSolver
  assertSuccess =<< SMTLIB2.runCommandString solver "(set-info :status sat)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(set-info :status unsat)"
  assertSuccess =<< SMTLIB2.runCommandString solver "(set-info :status unknown)"
  return ()

-- ---------------------------------------------------------------------

assertSuccess :: CmdResponse -> Assertion
assertSuccess (CmdGenResponse SMTLIB2.Success) = return ()
assertSuccess (CmdGenResponse Unsupported) = assertFailure "unsupported"
assertSuccess (CmdGenResponse (Error str)) = assertFailure ("(error " ++ str ++ ")")

-- ---------------------------------------------------------------------
-- Test harness

smtlib2SolverTestGroup :: TestTree
smtlib2SolverTestGroup = $(testGroupGenerator)
