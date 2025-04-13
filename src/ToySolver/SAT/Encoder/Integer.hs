{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Encoder.Integer
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Encoder.Integer
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
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC

newtype Expr = Expr SAT.PBSum
  deriving (Eq, Show, Read)

newVar :: SAT.AddPBNL m enc => enc -> Integer -> Integer -> m Expr
newVar enc lo hi
  | lo > hi = do
      SAT.addClause enc [] -- assert inconsistency
      return 0
  | lo == hi = return $ fromInteger lo
  | otherwise = do
      let hi' = hi - lo
          bitWidth = head $ [w | w <- [1..], let mx = 2 ^ w - 1, hi' <= mx]
      vs <- SAT.newVars enc (bitWidth - 1)
      v <- SAT.newVar enc
      return $ Expr $ [(lo,[]) | lo /= 0] ++ [(c,[x]) | (c,x) <- zip (iterate (2*) 1) vs] ++ [(hi' - (2 ^ (bitWidth - 1) - 1), [v])]

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

addConstraint :: SAT.AddPBNL m enc => enc -> OrdRel Expr -> m ()
addConstraint enc (OrdRel lhs op rhs) = do
  let Expr e = lhs - rhs
  case op of
    Le  -> SAT.addPBNLAtMost  enc e 0
    Lt  -> SAT.addPBNLAtMost  enc e (-1)
    Ge  -> SAT.addPBNLAtLeast enc e 0
    Gt  -> SAT.addPBNLAtLeast enc e 1
    Eql -> SAT.addPBNLExactly enc e 0
    NEq -> do
      sel <- SAT.newVar enc
      SAT.addPBNLAtLeastSoft enc sel e 1
      SAT.addPBNLAtMostSoft  enc (-sel) e (-1)

addConstraintSoft :: SAT.AddPBNL m enc => enc -> SAT.Lit -> OrdRel Expr -> m ()
addConstraintSoft enc sel (OrdRel lhs op rhs) = do
  let Expr e = lhs - rhs
  case op of
    Le  -> SAT.addPBNLAtMostSoft  enc sel e 0
    Lt  -> SAT.addPBNLAtMostSoft  enc sel e (-1)
    Ge  -> SAT.addPBNLAtLeastSoft enc sel e 0
    Gt  -> SAT.addPBNLAtLeastSoft enc sel e 1
    Eql -> SAT.addPBNLExactlySoft enc sel e 0
    NEq -> do
      sel2 <- SAT.newVar enc
      sel3 <- SAT.newVar enc
      sel4 <- SAT.newVar enc
      SAT.addClause enc [-sel, -sel2, sel3] -- sel ∧  sel2 → sel3
      SAT.addClause enc [-sel,  sel2, sel4] -- sel ∧ ¬sel2 → sel4
      SAT.addPBNLAtLeastSoft enc sel3 e 1
      SAT.addPBNLAtMostSoft  enc sel4 e (-1)

eval :: SAT.IModel m => m -> Expr -> Integer
eval m (Expr ts) = sum [if and [SAT.evalLit m lit | lit <- lits] then n else 0 | (n,lits) <- ts]
