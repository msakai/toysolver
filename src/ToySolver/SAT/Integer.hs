{-# LANGUAGE TypeFamilies #-}
module ToySolver.SAT.Integer
  ( Expr (..)
  , newVar
  , linearize
  , addConstraint
  , addConstraintSoft
  , eval
  ) where

import Control.Monad
import Data.Array.IArray
import Data.VectorSpace
import Text.Printf

import ToySolver.Data.ArithRel
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.TseitinEncoder as TseitinEncoder
import qualified ToySolver.SAT.PBNLC as PBNLC

newtype Expr = Expr PBNLC.PBSum

newVar :: SAT.Solver -> Integer -> Integer -> IO Expr
newVar solver lo hi
  | lo > hi = do
      SAT.addClause solver [] -- assert inconsistency
      return 0
  | lo == hi = return $ fromInteger lo
  | otherwise = do
      let hi' = hi - lo
          bitWidth = head $ [w | w <- [1..], let mx = 2 ^ w - 1, hi' <= mx]
      vs <- SAT.newVars solver bitWidth
      let xs = zip (iterate (2*) 1) vs
      SAT.addPBAtMost solver xs hi'
      return $ Expr ((lo,[]) : [(c,[x]) | (c,x) <- xs])

instance AdditiveGroup Expr where
  Expr xs1 ^+^ Expr xs2 = Expr (xs1++xs2)
  zeroV = Expr []
  negateV = ((-1) *^)

instance VectorSpace Expr where
  type Scalar Expr = Integer
  n *^ Expr xs = Expr [(n*m,lits) | (m,lits) <- xs]

instance Num Expr where
  Expr xs1 + Expr xs2 = Expr (xs1++xs2)
  Expr xs1 * Expr xs2 = Expr [(c1*c2, lits1++lits2) | (c1,lits1) <- xs1, (c2,lits2) <- xs2]
  negate (Expr xs) = Expr [(-c,lits) | (c,lits) <- xs]
  abs      = id
  signum _ = 1
  fromInteger c = Expr [(c,[])]

linearize :: TseitinEncoder.Encoder -> Expr -> IO (SAT.PBLinSum, Integer)
linearize enc (Expr xs) = do
  let ys = [(c,lits) | (c,lits@(_:_)) <- xs]
      c  = sum [c | (c,[]) <- xs]
  zs <- PBNLC.linearizePBSum enc ys
  return (zs, c)

addConstraint :: TseitinEncoder.Encoder -> ArithRel Expr -> IO ()
addConstraint enc (ArithRel lhs op rhs) = do
  let solver = TseitinEncoder.encSolver enc
  let Expr e = lhs - rhs
  case op of
    Le  -> PBNLC.addPBAtMost  enc e 0
    Lt  -> PBNLC.addPBAtMost  enc e (-1)
    Ge  -> PBNLC.addPBAtLeast enc e 0
    Gt  -> PBNLC.addPBAtLeast enc e 1
    Eql -> PBNLC.addPBExactly enc e 0
    NEq -> do
      sel <- SAT.newVar solver
      PBNLC.addPBAtLeastSoft enc sel e 1
      PBNLC.addPBAtMostSoft  enc (-sel) e (-1)

addConstraintSoft :: TseitinEncoder.Encoder -> SAT.Lit -> ArithRel Expr -> IO ()
addConstraintSoft enc sel (ArithRel lhs op rhs) = do
  let solver = TseitinEncoder.encSolver enc
  let Expr e = lhs - rhs
  case op of
    Le  -> PBNLC.addPBAtMostSoft  enc sel e 0
    Lt  -> PBNLC.addPBAtMostSoft  enc sel e (-1)
    Ge  -> PBNLC.addPBAtLeastSoft enc sel e 0
    Gt  -> PBNLC.addPBAtLeastSoft enc sel e 1
    Eql -> PBNLC.addPBExactlySoft enc sel e 0
    NEq -> do
      sel2 <- SAT.newVar solver
      sel3 <- TseitinEncoder.encodeConjWithPolarity enc TseitinEncoder.polarityNeg [sel,sel2]
      sel4 <- TseitinEncoder.encodeConjWithPolarity enc TseitinEncoder.polarityNeg [sel,-sel2]
      PBNLC.addPBAtLeastSoft enc sel3 e 1
      PBNLC.addPBAtMostSoft  enc sel4 e (-1)

eval :: SAT.IModel m => m -> Expr -> Integer
eval m (Expr ts) = sum [if and [SAT.evalLit m lit | lit <- lits] then n else 0 | (n,lits) <- ts]
