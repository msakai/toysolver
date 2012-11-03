{-# LANGUAGE MultiParamTypeClasses #-}
module SAT.Integer
  ( Expr (..)
  , newVar
  , constant
  , linearize
  , addLe
  , addGe
  , addEq
  , addLeSoft
  , addGeSoft
  , addEqSoft
  , eval
  ) where

import Control.Monad
import Data.Array.IArray
import Text.Printf
import qualified SAT
import qualified SAT.TseitinEncoder as TseitinEncoder
import Data.Linear

data Expr = Expr [(Integer, [SAT.Lit])]

newVar :: SAT.Solver -> Integer -> Integer -> IO Expr
newVar solver lo hi = do
  when (lo > hi) $ error $ printf "SAT.Integer.newVar: inconsistent bounds given [%d, %d]" lo hi
  let hi' = hi - lo
      bitWidth = head $ [w | w <- [1..], let mx = 2 ^ w - 1, hi' <= mx]
  vs <- replicateM bitWidth (SAT.newVar solver)
  let xs = zip (iterate (2*) 1) vs
  SAT.addPBAtMost solver xs hi'
  return $ Expr ((lo,[]) : [(c,[x]) | (c,x) <- xs])

constant :: Integer -> Expr
constant c = Expr [(c,[])]

instance Module Integer Expr where
  n .*. Expr xs = Expr [(n*m,lits) | (m,lits) <- xs]
  Expr xs1 .+. Expr xs2 = Expr (xs1++xs2)
  lzero = Expr []

instance Num Expr where
  Expr xs1 + Expr xs2 = Expr (xs1++xs2)
  Expr xs1 * Expr xs2 = Expr [(c1*c2, lits1++lits2) | (c1,lits1) <- xs1, (c2,lits2) <- xs2]
  negate (Expr xs) = Expr [(-c,lits) | (c,lits) <- xs]
  abs      = id
  signum _ = 1
  fromInteger c = Expr [(c,[])]

linearize :: TseitinEncoder.Encoder -> Expr -> IO ([(Integer,SAT.Lit)], Integer)
linearize enc (Expr xs) = do
  let ys = [(c,lits) | (c,lits@(_:_)) <- xs]
      c  = sum [c | (c,[]) <- xs]
  zs <- forM ys $ \(c,lits) -> do
    l <- TseitinEncoder.encodeConj enc lits
    return (c,l)
  return (zs, c)

addLe :: TseitinEncoder.Encoder -> Expr -> Expr -> IO ()
addLe enc lhs rhs = do
  let solver = TseitinEncoder.encSolver enc
  (xs,c) <- linearize enc (lhs - rhs)
  SAT.addPBAtMost solver xs (-c)

addGe :: TseitinEncoder.Encoder -> Expr -> Expr -> IO ()
addGe enc lhs rhs = do
  let solver = TseitinEncoder.encSolver enc
  (xs,c) <- linearize enc (lhs - rhs)
  SAT.addPBAtLeast solver xs (-c)

addEq :: TseitinEncoder.Encoder -> Expr -> Expr -> IO ()
addEq enc lhs rhs = do
  let solver = TseitinEncoder.encSolver enc
  (xs,c) <- linearize enc (lhs - rhs)
  SAT.addPBExactly solver xs (-c)

addLeSoft :: TseitinEncoder.Encoder -> SAT.Lit -> Expr -> Expr -> IO ()
addLeSoft enc ind lhs rhs = do
  let solver = TseitinEncoder.encSolver enc
  (xs,c) <- linearize enc (lhs - rhs)
  SAT.addPBAtMostSoft solver ind xs (-c)

addGeSoft :: TseitinEncoder.Encoder -> SAT.Lit -> Expr -> Expr -> IO ()
addGeSoft enc ind lhs rhs = do
  let solver = TseitinEncoder.encSolver enc
  (xs,c) <- linearize enc (lhs - rhs)
  SAT.addPBAtLeastSoft solver ind xs (-c)

addEqSoft :: TseitinEncoder.Encoder -> SAT.Lit -> Expr -> Expr -> IO ()
addEqSoft enc ind lhs rhs = do
  let solver = TseitinEncoder.encSolver enc
  (xs,c) <- linearize enc (lhs - rhs)
  SAT.addPBExactlySoft solver ind xs (-c)

eval :: SAT.Model -> Expr -> Integer
eval m (Expr ts) = sum [if and [m ! SAT.litVar lit == SAT.litPolarity lit | lit <- lits] then n else 0 | (n,lits) <- ts]
