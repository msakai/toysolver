{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  LPSolverHL
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- High-Level API for LPSolver.hs
--
-----------------------------------------------------------------------------

module LPSolverHL
  ( module Expr
  , module Formula
  , minimize
  , maximize
  , optimize
  , solve
  ) where

import Control.Monad.State
import Data.Maybe (fromMaybe)
import Data.Ratio
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

import Expr
import Formula
import LA
import qualified Simplex
import LPSolver

-- ---------------------------------------------------------------------------

maximize :: (Real r, Fractional r) => Expr r -> [Atom r] -> OptResult r
maximize = optimize False

minimize :: (Real r, Fractional r) => Expr r -> [Atom r] -> OptResult r
minimize = optimize True

optimize :: (Real r, Fractional r) => Bool -> Expr r -> [Atom r] -> OptResult r
optimize isMinimize obj2 cs2 = fromMaybe OptUnknown $ do
  obj <- compileExpr obj2  
  cs <- mapM compileAtom cs2
  return (twoPhasedSimplex' isMinimize obj cs)

solve :: (Real r, Fractional r) => [Atom r] -> SatResult r
solve cs2 = fromMaybe Unknown $ do
  cs <- mapM compileAtom cs2
  return (solve' cs)

-- ---------------------------------------------------------------------------

solve' :: (Real r, Fractional r) => [Constraint r] -> SatResult r
solve' cs =
  flip evalState (1 + maximum ((-1) : IS.toList vs), IM.empty, IS.empty, IM.empty) $ do
    tableau cs
    ret <- phaseI
    if not ret
      then return Unsat
      else do
        m <- getModel vs
        return (Sat m)
  where
    vs = vars cs

twoPhasedSimplex' :: (Real r, Fractional r) => Bool -> LC r -> [Constraint r] -> OptResult r
twoPhasedSimplex' isMinimize obj cs =
  flip evalState (1 + maximum ((-1) : IS.toList vs), IM.empty, IS.empty, IM.empty) $ do
    tableau cs
    ret <- phaseI
    if not ret
      then return OptUnsat
      else do
        ret2 <- simplex isMinimize obj
        if not ret2
          then return Unbounded
          else do
             m <- getModel vs
             tbl <- getTableau 
             return $ Optimum (Simplex.currentObjValue tbl) m
  where
    vs = vars cs `IS.union` vars obj

-- ---------------------------------------------------------------------------
-- Test cases

example_3_2 :: (Expr Rational, [Atom Rational])
example_3_2 = (obj, cond)
  where
    x1 = var 1
    x2 = var 2
    x3 = var 3
    obj = 3*x1 + 2*x2 + 3*x3
    cond = [ 2*x1 +   x2 +   x3 .<=. 2
           ,   x1 + 2*x2 + 3*x3 .<=. 5
           , 2*x1 + 2*x2 +   x3 .<=. 6
           , x1 .>=. 0
           , x2 .>=. 0
           , x3 .>=. 0
           ]

test_3_2 :: Bool
test_3_2 =
  uncurry maximize example_3_2 == 
  Optimum (27 % 5) (IM.fromList [(1,1 % 5),(2,0 % 1),(3,8 % 5)])

example_3_5 :: (Expr Rational, [Atom Rational])
example_3_5 = (obj, cond)
  where
    x1 = var 1
    x2 = var 2
    x3 = var 3
    x4 = var 4
    x5 = var 5
    obj = -2*x1 + 4*x2 + 7*x3 + x4 + 5*x5
    cond = [ -x1 +   x2 + 2*x3 +   x4 + 2*x5 .==. 7
           , -x1 + 2*x2 + 3*x3 +   x4 +   x5 .==. 6
           , -x1 +   x2 +   x3 + 2*x4 +   x5 .==. 4
           , x2 .>=. 0
           , x3 .>=. 0
           , x4 .>=. 0
           , x5 .>=. 0
           ]

test_3_5 :: Bool
test_3_5 =
  uncurry minimize example_3_5 ==
  Optimum (19 % 1) (IM.fromList [(1,(-1) % 1),(2,0 % 1),(3,1 % 1),(4,0 % 1),(5,2 % 1)]) 

example_4_1 :: (Expr Rational, [Atom Rational])
example_4_1 = (obj, cond)
  where
    x1 = var 1
    x2 = var 2
    obj = 2*x1 + x2
    cond = [ -x1 + x2 .>=. 2
           ,  x1 + x2 .<=. 1
           , x1 .>=. 0
           , x2 .>=. 0
           ]

test_4_1 :: Bool
test_4_1 =
  uncurry maximize example_4_1 ==
  OptUnsat

example_4_2 :: (Expr Rational, [Atom Rational])
example_4_2 = (obj, cond)
  where
    x1 = var 1
    x2 = var 2
    obj = 2*x1 + x2
    cond = [ - x1 - x2 .<=. 10
           , 2*x1 - x2 .<=. 40
           , x1 .>=. 0
           , x2 .>=. 0
           ]

test_4_2 :: Bool
test_4_2 =
  uncurry maximize example_4_2 ==
  Unbounded

example_4_3 :: (Expr Rational, [Atom Rational])
example_4_3 = (obj, cond)
  where
    x1 = var 1
    x2 = var 2
    obj = 6*x1 - 2*x2
    cond = [ 2*x1 - x2 .<=. 2
           , x1 .<=. 4
           , x1 .>=. 0
           , x2 .>=. 0
           ]

test_4_3 :: Bool
test_4_3 =
  uncurry maximize example_4_3 ==
  Optimum (12 % 1) (IM.fromList [(1,4 % 1),(2,6 % 1)])

example_4_5 :: (Expr Rational, [Atom Rational])
example_4_5 = (obj, cond)
  where
    x1 = var 1
    x2 = var 2
    obj = 2*x1 + x2
    cond = [ 4*x1 + 3*x2 .<=. 12
           , 4*x1 +   x2 .<=. 8
           , 4*x1 -   x2 .<=. 8
           , x1 .>=. 0
           , x2 .>=. 0
           ]

test_4_5 :: Bool
test_4_5 =
  uncurry maximize example_4_5 ==
  Optimum (5 % 1) (IM.fromList [(1,3 % 2),(2,2 % 1)])

example_4_6 :: (Expr Rational, [Atom Rational])
example_4_6 = (obj, cond)
  where
    x1 = var 1
    x2 = var 2
    x3 = var 3
    x4 = var 4
    obj = 20*x1 + (1/2)*x2 - 6*x3 + (3/4)*x4
    cond = [    x1 .<=. 2
           ,  8*x1 -       x2 + 9*x3 + (1/4)*x4 .<=. 16
           , 12*x1 - (1/2)*x2 + 3*x3 + (1/2)*x4 .<=. 24
           , x2 .<=. 1
           , x1 .>=. 0
           , x2 .>=. 0
           , x3 .>=. 0
           , x4 .>=. 0
           ]

test_4_6 :: Bool
test_4_6 =
  uncurry maximize example_4_6 ==
  Optimum (165 % 4) (IM.fromList [(1,2 % 1),(2,1 % 1),(3,0 % 1),(4,1 % 1)])

example_4_7 :: (Expr Rational, [Atom Rational])
example_4_7 = (obj, cond)
  where
    x1 = var 1
    x2 = var 2
    x3 = var 3
    x4 = var 4
    obj = x1 + 1.5*x2 + 5*x3 + 2*x4
    cond = [ 3*x1 + 2*x2 +   x3 + 4*x4 .<=. 6
           , 2*x1 +   x2 + 5*x3 +   x4 .<=. 4
           , 2*x1 + 6*x2 - 4*x3 + 8*x4 .==. 0
           ,   x1 + 3*x2 - 2*x3 + 4*x4 .==. 0
           , x1 .>=. 0
           , x2 .>=. 0
           , x3 .>=. 0
           , x4 .>=. 0
           ]

test_4_7 :: Bool
test_4_7 =
  uncurry maximize example_4_7 ==
  Optimum (48 % 11) (IM.fromList [(1,0 % 1),(2,0 % 1),(3,8 % 11),(4,4 % 11)])

testAll :: Bool
testAll = and
  [ test_3_2
  , test_3_5
  , test_4_1
  , test_4_2
  , test_4_3
  , test_4_5
  , test_4_6
  , test_4_7
  ]

-- ---------------------------------------------------------------------------
