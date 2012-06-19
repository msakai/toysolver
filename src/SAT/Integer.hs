{-# LANGUAGE MultiParamTypeClasses #-}
module SAT.Integer where

import Control.Monad
import Text.Printf
import SAT
import Data.Linear

data Expr = Expr [(Integer, SAT.Lit)] Integer

newVar :: SAT.Solver -> Integer -> Integer -> IO Expr
newVar solver lo hi = do
  when (lo > hi) $ error $ printf "SAT.Int.newInt: inconsistent bounds given [%d, %d]" lo hi
  let hi' = hi - lo
      bitWidth = head $ [w | w <- [1..], let mx = 2 ^ w - 1, hi' <= mx]
  vs <- replicateM bitWidth (SAT.newVar solver)
  let xs = zip (iterate (2*) 1) vs
  SAT.addPBAtMost solver xs hi'
  return $ Expr xs lo

constant :: Integer -> Expr
constant c = Expr [] c

instance Module Integer Expr where
  n .*. Expr xs c = Expr [(n*m,lit) | (m,lit) <- xs] (n*c)
  Expr xs1 c1 .+. Expr xs2 c2 = Expr (xs1++xs2) (c1+c2)
  lzero = Expr [] 0

addLe :: SAT.Solver -> Expr -> Expr -> IO ()
addLe solver lhs rhs = do
  let Expr xs c = lhs .-. rhs
  SAT.addPBAtMost solver xs (-c)

addGe :: SAT.Solver -> Expr -> Expr -> IO ()
addGe solver lhs rhs = do
  let Expr xs c = lhs .-. rhs
  SAT.addPBAtLeast solver xs (-c)

addEq :: SAT.Solver -> Expr -> Expr -> IO ()
addEq solver lhs rhs = do
  let Expr xs c = lhs .-. rhs
  SAT.addPBExactly solver xs (-c)

addLeSoft :: SAT.Solver -> SAT.Lit -> Expr -> Expr -> IO ()
addLeSoft solver ind lhs rhs = do
  let Expr xs c = lhs .-. rhs
  SAT.addPBAtMostSoft solver ind xs (-c)

addGeSoft :: SAT.Solver -> SAT.Lit -> Expr -> Expr -> IO ()
addGeSoft solver ind lhs rhs = do
  let Expr xs c = lhs .-. rhs
  SAT.addPBAtLeastSoft solver ind xs (-c)

addEqSoft :: SAT.Solver -> SAT.Lit -> Expr -> Expr -> IO ()
addEqSoft solver ind lhs rhs = do
  let Expr xs c = lhs .-. rhs
  SAT.addPBExactlySoft solver ind xs (-c)
