{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Test.SMT (smtTestGroup) where

import Control.Monad

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
  let c1 = ite a (2*x + (1/3)*y .<=. -4) (1.5 * y .==. -2*x)
      c2 = (x .>. y) .||. (a .<=>. (3*x .<. -1 + (1/5)*(x + y)))
  SMT.assert solver c1
  SMT.assert solver c2

  ret <- SMT.checkSAT solver
  ret @?= True

  m <- SMT.getModel solver
  SMT.eval m c1 @?= SMT.ValBool True
  SMT.eval m c2 @?= SMT.ValBool True

case_QF_EUF_1 :: IO ()
case_QF_EUF_1 = do
  solver <- SMT.newSolver
  x <- SMT.declareConst solver "x" SBool
  f <- SMT.declareFun solver "f" [SBool] SBool  

  let c1 = f true .==. true
      c2 = notB (f x)
  SMT.assert solver c1
  SMT.assert solver c2
  ret <- SMT.checkSAT solver
  ret @?= True

  m <- SMT.getModel solver
  SMT.eval m c1 @?= SMT.ValBool True
  SMT.eval m c2 @?= SMT.ValBool True
  
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

  let c1 = a .||. (x .==. y)
      c2 = f x ./=. f y
  SMT.assert solver c1
  SMT.assert solver c2
  ret <- SMT.checkSAT solver
  ret @?= True

  m <- SMT.getModel solver
  SMT.eval m c1 @?= SMT.ValBool True
  SMT.eval m c2 @?= SMT.ValBool True

  SMT.assert solver $ notB a
  ret <- SMT.checkSAT solver
  ret @?= False

case_QF_EUF_LRA :: IO ()
case_QF_EUF_LRA = do
  solver <- SMT.newSolver
  a <- SMT.declareConst solver "a" SReal
  b <- SMT.declareConst solver "b" SReal
  c <- SMT.declareConst solver "c" SReal
  f <- SMT.declareFun solver "f" [SReal] SReal
  g <- SMT.declareFun solver "g" [SReal] SReal
  h <- SMT.declareFun solver "h" [SReal, SReal] SReal

  let cs =
        [ 2*a .>=. b + f (g c)
        , f b .==. c
        , f c .==. a
        , g a .<. h a a
        , g b .>. h c b
        ]
  mapM_ (SMT.assert solver) cs

  ret <- SMT.checkSAT solver
  ret @?= True
  m <- SMT.getModel solver
  forM_ cs $ \c -> do
    SMT.eval m c @?= SMT.ValBool True

  SMT.assert solver $ b .==. c
  ret <- SMT.checkSAT solver
  ret @?= False

case_QF_EUF_Bool :: IO ()
case_QF_EUF_Bool = do
  solver <- SMT.newSolver
  a <- SMT.declareConst solver "a" SBool
  b <- SMT.declareConst solver "b" SBool
  c <- SMT.declareConst solver "c" SBool
  f <- SMT.declareFun solver "f" [SBool] SBool
  g <- SMT.declareFun solver "g" [SBool] SBool
  h <- SMT.declareFun solver "h" [SBool, SBool] SBool

  let cs =
        [ f b .==. c
        , f c .==. a
        , g a .==. h a a
        , g b ./=. h c b
        ]
  mapM_ (SMT.assert solver) cs

  ret <- SMT.checkSAT solver
  ret @?= True
  m <- SMT.getModel solver
  forM_ cs $ \c -> do
    SMT.eval m c @?= SMT.ValBool True

  SMT.assert solver $ b .==. c
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
