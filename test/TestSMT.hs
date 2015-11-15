{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module TestSMT (smtTestGroup) where

import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import ToySolver.Data.Boolean
import ToySolver.Data.ArithRel
import ToySolver.SMT (Expr (..), Sort (..))
import qualified ToySolver.SMT as SMT

-- -------------------------------------------------------------------

case_QF_LRA :: IO ()
case_QF_LRA = do
  solver <- SMT.newSolver

  a <- SMT.declareConst solver "a" SBool
  x <- SMT.declareConst solver "x" SReal
  y <- SMT.declareConst solver "y" SReal
  SMT.assert solver $ ite a (2*x + (1/3)*y .<=. -4) (1.5 * y .==. -2*x)
  SMT.assert solver $ (x .>. y) .||. (a .<=>. (3*x .<. -1 + (1/5)*(x + y)))

  ret <- SMT.checkSAT solver
  ret @?= True

case_QF_EUF_1 :: IO ()
case_QF_EUF_1 = do
  solver <- SMT.newSolver
  x <- SMT.declareConst solver "x" SBool
  f <- SMT.declareFun solver "f" [SBool] SBool  

  SMT.assert solver $ f true .==. true
  SMT.assert solver $ notB (f x)
  ret <- SMT.checkSAT solver
  ret @?= True
  
  SMT.assert solver $ x
  ret <- SMT.checkSAT solver
  ret @?= False

case_QF_EUF_2 :: IO ()
case_QF_EUF_2 = do
  solver <- SMT.newSolver

  a <- SMT.declareConst solver "a" SBool
  x <- SMT.declareConst solver "x" SU
  y <- SMT.declareConst solver "y" SU
  f <- SMT.declareFun solver "f" [SU] SU  

  SMT.assert solver $ a .||. (x .==. y)
  SMT.assert solver $ f x ./=. f y
  ret <- SMT.checkSAT solver
  ret @?= True

  SMT.assert solver $ notB a
  ret <- SMT.checkSAT solver
  ret @?= False

case_pushContext :: IO ()
case_pushContext = do
  solver <- SMT.newSolver
  x <- SMT.declareConst solver "x" SU
  y <- SMT.declareConst solver "y" SU
  f <- SMT.declareFun solver "f" [SU] SU

  SMT.assert solver $ f x ./=. f y
  ret <- SMT.checkSAT solver
  ret @?= True

  SMT.pushContext solver
  SMT.assert solver $ x .==. y
  ret <- SMT.checkSAT solver
  ret @?= False
  SMT.popContext solver

  ret <- SMT.checkSAT solver
  ret @?= True

------------------------------------------------------------------------
-- Test harness

smtTestGroup :: TestTree
smtTestGroup = $(testGroupGenerator)
