{-# LANGUAGE TemplateHaskell #-}
module Main (main) where

import Control.Monad
import Data.List
import qualified Data.IntMap as IM
import qualified Data.Map as Map
import Test.HUnit hiding (Test)
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.TH
import Test.Framework.Providers.HUnit

import Data.AlgebraicNumber
import Data.ArithRel
import Data.Expr
import Data.Formula
import Data.Linear
import qualified Data.LA as LA
import qualified Data.Polynomial as P
import Data.OptDir

import qualified FourierMotzkin
import qualified OmegaTest
import qualified Cooper
import qualified CAD
import qualified Simplex2
import qualified ContiTraverso

------------------------------------------------------------------------

{-
Example from the OmegaTest paper

7x + 12y + 31z = 17
3x + 5y + 14z = 7
1 ≤ x ≤ 40
-50 ≤ y ≤ 50

satisfiable in R
satisfiable in Z

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (= (+ (* 7 x) (* 12 y) (* 31 z)) 17))
(assert (= (+ (* 3 x) (* 5 y) (* 14 z)) 7))
(assert (<= 1 x))
(assert (<= x 40))
(assert (<= (- 50) y))
(assert (<= y 50))
(check-sat) ; => sat
(get-model)

Just (DNF {unDNF = [[Nonneg (fromTerms [(-17,-1),(7,0),(12,1),(31,2)]),Nonneg (fromTerms [(17,-1),(-7,0),(-12,1),(-31,2)]),Nonneg (fromTerms [(-7,-1),(3,0),(5,1),(14,2)]),Nonneg (fromTerms [(7,-1),(-3,0),(-5,1),(-14,2)]),Nonneg (fromTerms [(-1,-1),(1,0)]),Nonneg (fromTerms [(40,-1),(-1,0)]),Nonneg (fromTerms [(50,-1),(1,1)]),Nonneg (fromTerms [(50,-1),(-1,1)])]]})

7x+12y+31z  - 17 >= 0
-7x-12y-31z + 17 >= 0
3x+5y+14z - 7  >= 0
-3x-5y-14z + 7 >= 0
x - 1 >= 0
-x + 40 >= 0
y + 50  >= 0
-y + 50 >= 0
-}
test1 :: Formula (Atom Rational)
test1 = c1 .&&. c2 .&&. c3 .&&. c4
  where
    x = Var 0
    y = Var 1
    z = Var 2
    c1 = 7*x + 12*y + 31*z .==. 17
    c2 = 3*x + 5*y + 14*z .==. 7
    c3 = 1 .<=. x .&&. x .<=. 40
    c4 = (-50) .<=. y .&&. y .<=. 50

test1' :: [LA.Atom Rational]
test1' = [c1, c2] ++ c3 ++ c4
  where
    x = LA.var 0
    y = LA.var 1
    z = LA.var 2
    c1 = 7.*.x .+. 12.*.y .+. 31.*.z .==. LA.constant 17
    c2 = 3.*.x .+. 5.*.y .+. 14.*.z .==. LA.constant 7
    c3 = [LA.constant 1 .<=. x, x .<=. LA.constant 40]
    c4 = [LA.constant (-50) .<=. y, y .<=. LA.constant 50]


{-
Example from the OmegaTest paper

27 ≤ 11x+13y ≤ 45
-10 ≤ 7x-9y ≤ 4

satisfiable in R
but unsatisfiable in Z

(declare-fun x () Int)
(declare-fun y () Int)
(define-fun t1 () Int (+ (* 11 x) (* 13 y)))
(define-fun t2 () Int (- (* 7 x) (* 9 y)))
(assert (<= 27 t1))
(assert (<= t1 45))
(assert (<= (- 10) t2))
(assert (<= t2 4))
(check-sat) ; unsat
(get-model)
-}
test2 :: Formula (Atom Rational)
test2 = c1 .&&. c2
  where
    x = Var 0
    y = Var 1
    t1 = 11*x + 13*y
    t2 = 7*x - 9*y
    c1 = 27 .<=. t1 .&&. t1 .<=. 45
    c2 = (-10) .<=. t2 .&&. t2 .<=. 4

test2' :: [LA.Atom Rational]
test2' =
  [ LA.constant 27 .<=. t1
  , t1 .<=. LA.constant 45
  , LA.constant (-10) .<=. t2
  , t2 .<=. LA.constant 4
  ]
  where
    x = LA.var 0
    y = LA.var 1
    t1 = 11.*.x .+. 13.*.y
    t2 = 7.*.x .-. 9.*.y

------------------------------------------------------------------------

case_FourierMotzkin_test1 :: IO ()
case_FourierMotzkin_test1 = 
  case FourierMotzkin.solveConj test1' of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  ->
      forM_ test1' $ \a -> do
        LA.evalAtom m a @?= True

case_FourierMotzkin_test2 :: IO ()
case_FourierMotzkin_test2 = 
  case FourierMotzkin.solveConj test2' of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  ->
      forM_ test2' $ \a -> do
        LA.evalAtom m a @?= True

------------------------------------------------------------------------

case_CAD_test1 :: IO ()
case_CAD_test1 = 
  case CAD.solve test1'' of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  ->
      forM_ test1'' $ \a -> do
        evalPAtom m a @?= True
  where
    test1'' = map toPRel test1'

case_CAD_test2 :: IO ()
case_CAD_test2 = 
  case CAD.solve test2'' of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  ->
      forM_ test2'' $ \a -> do
        evalPAtom m a @?= True
  where
    test2'' = map toPRel test2'

toP :: LA.Expr Rational -> P.Polynomial Rational Int
toP e = P.fromTerms [(c, if x == LA.unitVar then P.mmOne else P.mmVar x) | (c,x) <- LA.terms e]

toPRel :: LA.Atom Rational -> Rel (P.Polynomial Rational Int)
toPRel (Rel lhs op rhs) = Rel (toP lhs) op (toP rhs)  

evalP :: Map.Map Int AReal -> P.Polynomial Rational Int -> AReal
evalP m p = P.eval (m Map.!) $ P.mapCoeff fromRational p

evalPAtom :: Map.Map Int AReal -> Rel (P.Polynomial Rational Int) -> Bool
evalPAtom m (Rel lhs op rhs) =　evalOp op (evalP m lhs) (evalP m rhs)

------------------------------------------------------------------------

case_OmegaTest_test1 :: IO ()
case_OmegaTest_test1 = 
  case OmegaTest.solve test1' of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  -> do
      forM_ test1' $ \a -> do
        LA.evalAtom (IM.map fromInteger m) a @?= True

case_OmegaTest_test2 :: IO ()
case_OmegaTest_test2 = 
  case OmegaTest.solve test2' of
    Just _  -> assertFailure "expected: Nothing\n but got: Just"
    Nothing -> return ()

------------------------------------------------------------------------

case_Cooper_test1 :: IO ()
case_Cooper_test1 = 
  case Cooper.solveConj test1' of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  -> do
      forM_ test1' $ \a -> do
        LA.evalAtom (IM.map fromInteger m) a @?= True

case_Cooper_test2 :: IO ()
case_Cooper_test2 = 
  case Cooper.solveConj test2' of
    Just _  -> assertFailure "expected: Nothing\n but got: Just"
    Nothing -> return ()

------------------------------------------------------------------------

case_Simplex2_test1 :: IO ()
case_Simplex2_test1 = do
  solver <- Simplex2.newSolver
  replicateM 3 (Simplex2.newVar solver) -- XXX
  mapM_ (Simplex2.assertAtomEx solver) test1'
  ret <- Simplex2.check solver
  ret @?= True

case_Simplex2_test2 :: IO ()
case_Simplex2_test2 = do
  solver <- Simplex2.newSolver
  replicateM 2 (Simplex2.newVar solver) -- XXX
  mapM_ (Simplex2.assertAtomEx solver) test2'
  ret <- Simplex2.check solver
  ret @?= True

------------------------------------------------------------------------

-- Too slow

disabled_case_ContiTraverso_test1 :: IO ()
disabled_case_ContiTraverso_test1 = 
  case ContiTraverso.solve P.grlex OptMin (LA.constant 0) test1' of
    Nothing -> assertFailure "expected: Just\n but got: Nothing"
    Just m  -> do
      forM_ test1' $ \a -> do
        LA.evalAtom (IM.map fromInteger m) a @?= True

disabled_case_ContiTraverso_test2 :: IO ()
disabled_case_ContiTraverso_test2 = 
  case ContiTraverso.solve P.grlex OptMin (LA.constant 0) test2' of
    Just _  -> assertFailure "expected: Nothing\n but got: Just"
    Nothing -> return ()

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
