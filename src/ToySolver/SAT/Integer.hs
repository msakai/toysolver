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

data Expr = Expr [(Integer, [SAT.Lit])]

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
  zs <- forM ys $ \(c,lits) -> do
    l <- TseitinEncoder.encodeConj enc lits
    return (c,l)
  return (zs, c)

addConstraint :: TseitinEncoder.Encoder -> Rel Expr -> IO ()
addConstraint enc (Rel lhs op rhs) = do
  let solver = TseitinEncoder.encSolver enc
  (lhs2,c) <- linearize enc (lhs - rhs)
  let rhs2 = -c
  case op of
    Le  -> SAT.addPBAtMost  solver lhs2 rhs2
    Lt  -> SAT.addPBAtMost  solver lhs2 (rhs2-1)
    Ge  -> SAT.addPBAtLeast solver lhs2 rhs2
    Gt  -> SAT.addPBAtLeast solver lhs2 (rhs2+1)
    Eql -> SAT.addPBExactly solver lhs2 rhs2
    NEq -> do
      sel <- SAT.newVar solver
      SAT.addPBAtLeastSoft solver sel lhs2 (rhs2+1)
      SAT.addPBAtMostSoft  solver (-sel) lhs2 (rhs2-1)

addConstraintSoft :: TseitinEncoder.Encoder -> SAT.Lit -> Rel Expr -> IO ()
addConstraintSoft enc sel (Rel lhs op rhs) = do
  let solver = TseitinEncoder.encSolver enc
  (lhs2,c) <- linearize enc (lhs - rhs)
  let rhs2 = -c
  case op of
    Le  -> SAT.addPBAtMostSoft  solver sel lhs2 rhs2
    Lt  -> SAT.addPBAtMostSoft  solver sel lhs2 (rhs2-1)
    Ge  -> SAT.addPBAtLeastSoft solver sel lhs2 rhs2
    Gt  -> SAT.addPBAtLeastSoft solver sel lhs2 (rhs2+1)
    Eql -> SAT.addPBExactlySoft solver sel lhs2 rhs2
    NEq -> do
      sel2 <- SAT.newVar solver
      sel3 <- TseitinEncoder.encodeConj enc [sel,sel2]
      sel4 <- TseitinEncoder.encodeConj enc [sel,-sel2]
      SAT.addPBAtLeastSoft solver sel3 lhs2 (rhs2+1)
      SAT.addPBAtMostSoft  solver sel4 lhs2 (rhs2-1)

eval :: SAT.IModel m => m -> Expr -> Integer
eval m (Expr ts) = sum [if and [SAT.evalLit m lit | lit <- lits] then n else 0 | (n,lits) <- ts]
