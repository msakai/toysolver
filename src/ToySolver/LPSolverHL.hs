{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.LPSolverHL
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables)
--
-- High-Level API for LPSolver.hs
--
-----------------------------------------------------------------------------

module ToySolver.LPSolverHL
  ( OptResult (..)
  , minimize
  , maximize
  , optimize
  , solve
  ) where

import Control.Monad.State
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.OptDir
import Data.VectorSpace

import ToySolver.Data.ArithRel
import qualified ToySolver.Data.LA as LA
import ToySolver.Data.Var
import qualified ToySolver.Simplex as Simplex
import ToySolver.LPSolver

-- ---------------------------------------------------------------------------

-- | results of optimization
data OptResult r = OptUnsat | Unbounded | Optimum r (Model r)
  deriving (Show, Eq, Ord)

maximize :: (RealFrac r) => LA.Expr r -> [LA.Atom r] -> OptResult r
maximize = optimize OptMax

minimize :: (RealFrac r) => LA.Expr r -> [LA.Atom r] -> OptResult r
minimize = optimize OptMin

solve :: (RealFrac r) => [LA.Atom r] -> Maybe (Model r)
solve cs =
  flip evalState (emptySolver vs) $ do
    tableau cs
    ret <- phaseI
    if not ret
      then return Nothing
      else do
        m <- getModel vs
        return (Just m)
  where
    vs = vars cs

optimize :: (RealFrac r) => OptDir -> LA.Expr r -> [LA.Atom r] -> OptResult r
optimize optdir obj cs =
  flip evalState (emptySolver vs) $ do
    tableau cs
    ret <- phaseI
    if not ret
      then return OptUnsat
      else do
        ret2 <- simplex optdir obj
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

example_3_2 :: (LA.Expr Rational, [LA.Atom Rational])
example_3_2 = (obj, cond)
  where
    x1 = LA.var 1
    x2 = LA.var 2
    x3 = LA.var 3
    obj = 3*^x1 ^+^ 2*^x2 ^+^ 3*^x3
    cond = [ 2*^x1 ^+^    x2 ^+^    x3 .<=. LA.constant 2
           ,    x1 ^+^ 2*^x2 ^+^ 3*^x3 .<=. LA.constant 5
           , 2*^x1 ^+^ 2*^x2 ^+^    x3 .<=. LA.constant 6
           , x1 .>=. LA.constant 0
           , x2 .>=. LA.constant 0
           , x3 .>=. LA.constant 0
           ]

test_3_2 :: Bool
test_3_2 =
  uncurry maximize example_3_2 == 
  Optimum (27/5) (IM.fromList [(1,1/5),(2,0),(3,8/5)])

example_3_5 :: (LA.Expr Rational, [LA.Atom Rational])
example_3_5 = (obj, cond)
  where
    x1 = LA.var 1
    x2 = LA.var 2
    x3 = LA.var 3
    x4 = LA.var 4
    x5 = LA.var 5
    obj = (-2)*^x1 ^+^ 4*^x2 ^+^ 7*^x3 ^+^ x4 ^+^ 5*^x5
    cond = [ (-1)*^x1 ^+^    x2 ^+^ 2*^x3 ^+^    x4 ^+^ 2*^x5 .==. LA.constant 7
           , (-1)*^x1 ^+^ 2*^x2 ^+^ 3*^x3 ^+^    x4 ^+^    x5 .==. LA.constant 6
           , (-1)*^x1 ^+^    x2 ^+^    x3 ^+^ 2*^x4 ^+^    x5 .==. LA.constant 4
           , x2 .>=. LA.constant 0
           , x3 .>=. LA.constant 0
           , x4 .>=. LA.constant 0
           , x5 .>=. LA.constant 0
           ]

test_3_5 :: Bool
test_3_5 =
  uncurry minimize example_3_5 ==
  Optimum 19 (IM.fromList [(1,-1),(2,0),(3,1),(4,0),(5,2)])

example_4_1 :: (LA.Expr Rational, [LA.Atom Rational])
example_4_1 = (obj, cond)
  where
    x1 = LA.var 1
    x2 = LA.var 2
    obj = 2*^x1 ^+^ x2
    cond = [ (-1)*^x1 ^+^ x2 .>=. LA.constant 2
           ,       x1 ^+^ x2 .<=. LA.constant 1
           , x1 .>=. LA.constant 0
           , x2 .>=. LA.constant 0
           ]

test_4_1 :: Bool
test_4_1 =
  uncurry maximize example_4_1 ==
  OptUnsat

example_4_2 :: (LA.Expr Rational, [LA.Atom Rational])
example_4_2 = (obj, cond)
  where
    x1 = LA.var 1
    x2 = LA.var 2
    obj = 2*^x1 ^+^ x2
    cond = [ (-1)*^x1 ^-^ x2 .<=. LA.constant 10
           ,    2*^x1 ^-^ x2 .<=. LA.constant 40
           , x1 .>=. LA.constant 0
           , x2 .>=. LA.constant 0
           ]

test_4_2 :: Bool
test_4_2 =
  uncurry maximize example_4_2 ==
  Unbounded

example_4_3 :: (LA.Expr Rational, [LA.Atom Rational])
example_4_3 = (obj, cond)
  where
    x1 = LA.var 1
    x2 = LA.var 2
    obj = 6*^x1 ^-^ 2*^x2
    cond = [ 2*^x1 ^-^ x2 .<=. LA.constant 2
           , x1 .<=. LA.constant 4
           , x1 .>=. LA.constant 0
           , x2 .>=. LA.constant 0
           ]

test_4_3 :: Bool
test_4_3 =
  uncurry maximize example_4_3 ==
  Optimum 12 (IM.fromList [(1,4),(2,6)])

example_4_5 :: (LA.Expr Rational, [LA.Atom Rational])
example_4_5 = (obj, cond)
  where
    x1 = LA.var 1
    x2 = LA.var 2
    obj = 2*^x1 ^+^ x2
    cond = [ 4*^x1 ^+^ 3*^x2 .<=. LA.constant 12
           , 4*^x1 ^+^    x2 .<=. LA.constant 8
           , 4*^x1 ^-^    x2 .<=. LA.constant 8
           , x1 .>=. LA.constant 0
           , x2 .>=. LA.constant 0
           ]

test_4_5 :: Bool
test_4_5 =
  uncurry maximize example_4_5 ==
  Optimum 5 (IM.fromList [(1,3/2),(2,2)])

example_4_6 :: (LA.Expr Rational, [LA.Atom Rational])
example_4_6 = (obj, cond)
  where
    x1 = LA.var 1
    x2 = LA.var 2
    x3 = LA.var 3
    x4 = LA.var 4
    obj = 20*^x1 ^+^ (1/2)*^x2 ^-^ 6*^x3 ^+^ (3/4)*^x4
    cond = [     x1 .<=. LA.constant 2
           ,  8*^x1 ^-^        x2 ^+^ 9*^x3 ^+^ (1/4)*^x4 .<=. LA.constant 16
           , 12*^x1 ^-^ (1/2)*^x2 ^+^ 3*^x3 ^+^ (1/2)*^x4 .<=. LA.constant 24
           , x2 .<=. LA.constant 1
           , x1 .>=. LA.constant 0
           , x2 .>=. LA.constant 0
           , x3 .>=. LA.constant 0
           , x4 .>=. LA.constant 0
           ]

test_4_6 :: Bool
test_4_6 =
  uncurry maximize example_4_6 ==
  Optimum (165/4) (IM.fromList [(1,2),(2,1),(3,0),(4,1)])

example_4_7 :: (LA.Expr Rational, [LA.Atom Rational])
example_4_7 = (obj, cond)
  where
    x1 = LA.var 1
    x2 = LA.var 2
    x3 = LA.var 3
    x4 = LA.var 4
    obj = x1 ^+^ 1.5*^x2 ^+^ 5*^x3 ^+^ 2*^x4
    cond = [ 3*^x1 ^+^ 2*^x2 ^+^    x3 ^+^ 4*^x4 .<=. LA.constant 6
           , 2*^x1 ^+^    x2 ^+^ 5*^x3 ^+^    x4 .<=. LA.constant 4
           , 2*^x1 ^+^ 6*^x2 ^-^ 4*^x3 ^+^ 8*^x4 .==. LA.constant 0
           ,    x1 ^+^ 3*^x2 ^-^ 2*^x3 ^+^ 4*^x4 .==. LA.constant 0
           , x1 .>=. LA.constant 0
           , x2 .>=. LA.constant 0
           , x3 .>=. LA.constant 0
           , x4 .>=. LA.constant 0
           ]

test_4_7 :: Bool
test_4_7 =
  uncurry maximize example_4_7 ==
  Optimum (48/11) (IM.fromList [(1,0),(2,0),(3,81),(4,41)])

-- 退化して巡回の起こるKuhnの7変数3制約の例
kuhn_7_3 :: (LA.Expr Rational, [LA.Atom Rational])
kuhn_7_3 = (obj, cond)
  where
    [x1,x2,x3,x4,x5,x6,x7] = map LA.var [1..7]
    obj = (-2)*^x4 ^+^ (-3)*^x5 ^+^ x6 ^+^ 12*^x7
    cond = [ x1 ^-^     2*^x4 ^-^ 9*^x5 ^+^        x6 ^+^   9*^x7 .==. LA.constant 0
           , x2 ^+^ (1/3)*^x4 ^+^    x5 ^-^ (1/3)*^x6 ^-^   2*^x7 .==. LA.constant 0
           , x3 ^+^     2*^x4 ^+^ 3*^x5 ^-^        x6 ^-^  12*^x7 .==. LA.constant 2
           , x1 .>=. LA.constant 0
           , x2 .>=. LA.constant 0
           , x3 .>=. LA.constant 0
           , x4 .>=. LA.constant 0
           , x5 .>=. LA.constant 0
           , x6 .>=. LA.constant 0
           , x7 .>=. LA.constant 0
           ]

test_kuhn_7_3 :: Bool
test_kuhn_7_3 =
  uncurry minimize kuhn_7_3 ==
  Optimum (-2) (IM.fromList [(1,2),(2,0),(3,0),(4,2),(5,0),(6,2),(7,0)])

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
  , test_kuhn_7_3
  ]

-- ---------------------------------------------------------------------------
