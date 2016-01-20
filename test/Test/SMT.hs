{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Test.SMT (smtTestGroup) where

import Control.Exception (evaluate)
import Control.Monad

import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import ToySolver.Data.Boolean
import ToySolver.Data.OrdRel
import ToySolver.SMT (Expr (..))
import qualified ToySolver.SMT as SMT

-- -------------------------------------------------------------------

case_QF_LRA :: IO ()
case_QF_LRA = do
  solver <- SMT.newSolver

  a <- SMT.declareConst solver "a" SMT.sBool
  x <- SMT.declareConst solver "x" SMT.sReal
  y <- SMT.declareConst solver "y" SMT.sReal
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
  x <- SMT.declareConst solver "x" SMT.sBool
  f <- SMT.declareFun solver "f" [SMT.sBool] SMT.sBool  

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
  sU <- SMT.declareSort solver "U" 0

  a <- SMT.declareConst solver "a" SMT.sBool
  x <- SMT.declareConst solver "x" sU
  y <- SMT.declareConst solver "y" sU
  f <- SMT.declareFun solver "f" [sU] sU  

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
  a <- SMT.declareConst solver "a" SMT.sReal
  b <- SMT.declareConst solver "b" SMT.sReal
  c <- SMT.declareConst solver "c" SMT.sReal
  f <- SMT.declareFun solver "f" [SMT.sReal] SMT.sReal
  g <- SMT.declareFun solver "g" [SMT.sReal] SMT.sReal
  h <- SMT.declareFun solver "h" [SMT.sReal, SMT.sReal] SMT.sReal

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
  a <- SMT.declareConst solver "a" SMT.sBool
  b <- SMT.declareConst solver "b" SMT.sBool
  c <- SMT.declareConst solver "c" SMT.sBool
  f <- SMT.declareFun solver "f" [SMT.sBool] SMT.sBool
  g <- SMT.declareFun solver "g" [SMT.sBool] SMT.sBool
  h <- SMT.declareFun solver "h" [SMT.sBool, SMT.sBool] SMT.sBool

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

case_push :: IO ()
case_push = do
  solver <- SMT.newSolver
  sU <- SMT.declareSort solver "U" 0

  x <- SMT.declareConst solver "x" sU
  y <- SMT.declareConst solver "y" sU
  f <- SMT.declareFun solver "f" [sU] sU

  SMT.assert solver $ f x ./=. f y
  ret <- SMT.checkSAT solver
  ret @?= True

  SMT.push solver
  SMT.assert solver $ x .==. y
  ret <- SMT.checkSAT solver
  ret @?= False
  SMT.pop solver

  ret <- SMT.checkSAT solver
  ret @?= True

case_QF_LRA_division_by_zero :: IO ()
case_QF_LRA_division_by_zero = do
  solver <- SMT.newSolver

  x1 <- SMT.declareConst solver "x1" SMT.sReal
  x2 <- SMT.declareConst solver "x2" SMT.sReal
  let y1 = x1 / 0
      y2 = x2 / 0

  ret <- SMT.checkSAT solver
  ret @?= True
  m <- SMT.getModel solver
  evaluate $ SMT.eval m y1
  evaluate $ SMT.eval m y2

  SMT.assert solver $ y1 ./=. y2
  ret <- SMT.checkSAT solver
  ret @?= True
  m <- SMT.getModel solver

  SMT.assert solver $ x1 .==. x2
  ret <- SMT.checkSAT solver
  ret @?= False

case_LRA_model_construction_bug :: IO ()
case_LRA_model_construction_bug = do
  solver <- SMT.newSolver
  cond <- SMT.declareConst solver "cond" SMT.sBool
  a <- SMT.declareConst solver "a" SMT.sReal
  b <- SMT.declareConst solver "b" SMT.sReal
  let cs = [ a .<. 10
           , b .<. 10
           , cond .=>. a+b .>. 14
           , cond .=>. a+b .<. 15
           ]
  forM_ cs $ SMT.assert solver
  ret <- SMT.checkSATAssuming solver [cond]
  m <- SMT.getModel solver 
  forM_ cs $ \c -> do
    let val = SMT.eval m c
    -- unless (val == SMT.ValBool True) $ print val
    val @?= SMT.ValBool True
{-
The solving process goes like the following.

  ASSERT: a <= 10 - delta
  ASSERT: b <= 10 - delta
  PUSH
  ASSERT a+b <= 15 - delta
  ASSERT a+b >= 14 + delta

This produces assignment

  a+b = 14 + delta
  a   = 10 - delta
  b   = (a+b) - a = (14 + delta) - (10 - delta) = 4 + 2 delta

OR alternatively

  a+b = 14 + delta
  b   = 10 - delta
  a   = (a+b) - b = (14 + delta) - (10 - delta) = 4 + 2 delta.

The delta value should be in the range (0, min{(15-14)/2, (10-4)/3}] = (0, 1/2]
to satisfy the constraints. But if we were compute it after backtracking, the
range of delta becomes (0, (10-4)/3] = (0,2] and choosing delta=2 causes
violation of a+b < 15.
-}

------------------------------------------------------------------------
-- Test harness

smtTestGroup :: TestTree
smtTestGroup = $(testGroupGenerator)
