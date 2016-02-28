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
import Control.Monad.Primitive
import Data.Array.IArray
import Data.VectorSpace
import Text.Printf

import ToySolver.Data.OrdRel
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.TseitinEncoder as TseitinEncoder
import qualified ToySolver.SAT.PBNLC as PBNLC

newtype Expr = Expr PBNLC.PBSum

newVar :: PrimMonad m => PBNLC.Encoder m -> Integer -> Integer -> m Expr
newVar enc lo hi
  | lo > hi = do
      SAT.addClause enc [] -- assert inconsistency
      return 0
  | lo == hi = return $ fromInteger lo
  | otherwise = do
      let hi' = hi - lo
          bitWidth = head $ [w | w <- [1..], let mx = 2 ^ w - 1, hi' <= mx]
      vs <- SAT.newVars enc bitWidth
      let xs = zip (iterate (2*) 1) vs
      SAT.addPBAtMost enc xs hi'
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

linearize :: PrimMonad m => PBNLC.Encoder m -> Expr -> m (SAT.PBLinSum, Integer)
linearize enc (Expr xs) = do
  let ys = [(c,lits) | (c,lits@(_:_)) <- xs]
      c  = sum [c | (c,[]) <- xs]
  zs <- PBNLC.linearizePBSum enc ys
  return (zs, c)

addConstraint :: PrimMonad m => PBNLC.Encoder m -> OrdRel Expr -> m ()
addConstraint enc (OrdRel lhs op rhs) = do
  let Expr e = lhs - rhs
  case op of
    Le  -> PBNLC.addPBNLAtMost  enc e 0
    Lt  -> PBNLC.addPBNLAtMost  enc e (-1)
    Ge  -> PBNLC.addPBNLAtLeast enc e 0
    Gt  -> PBNLC.addPBNLAtLeast enc e 1
    Eql -> PBNLC.addPBNLExactly enc e 0
    NEq -> do
      sel <- SAT.newVar enc
      PBNLC.addPBNLAtLeastSoft enc sel e 1
      PBNLC.addPBNLAtMostSoft  enc (-sel) e (-1)

addConstraintSoft :: PrimMonad m => PBNLC.Encoder m -> SAT.Lit -> OrdRel Expr -> m ()
addConstraintSoft enc sel (OrdRel lhs op rhs) = do
  let Expr e = lhs - rhs
  case op of
    Le  -> PBNLC.addPBNLAtMostSoft  enc sel e 0
    Lt  -> PBNLC.addPBNLAtMostSoft  enc sel e (-1)
    Ge  -> PBNLC.addPBNLAtLeastSoft enc sel e 0
    Gt  -> PBNLC.addPBNLAtLeastSoft enc sel e 1
    Eql -> PBNLC.addPBNLExactlySoft enc sel e 0
    NEq -> do
      sel2 <- SAT.newVar enc
      sel3 <- TseitinEncoder.encodeConjWithPolarity (PBNLC.getTseitinEncoder enc) TseitinEncoder.polarityNeg [sel,sel2]
      sel4 <- TseitinEncoder.encodeConjWithPolarity (PBNLC.getTseitinEncoder enc) TseitinEncoder.polarityNeg [sel,-sel2]
      PBNLC.addPBNLAtLeastSoft enc sel3 e 1
      PBNLC.addPBNLAtMostSoft  enc sel4 e (-1)

eval :: SAT.IModel m => m -> Expr -> Integer
eval m (Expr ts) = sum [if and [SAT.evalLit m lit | lit <- lits] then n else 0 | (n,lits) <- ts]
