{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.FOL.Arith
-- Copyright   :  (c) Masahiro Sakai 2011-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Arithmetic language (not limited to linear ones).
-- 
-----------------------------------------------------------------------------
module ToySolver.Data.FOL.Arith
  (
  -- * Arithmetic expressions
    Expr (..)
  , var
  , evalExpr

  -- * Atomic formula
  , module ToySolver.Data.OrdRel
  , Atom (..)
  , evalAtom

  -- * Arithmetic formula
  , module ToySolver.Data.FOL.Formula

  -- * Misc
  , SatResult (..)
  ) where

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.Ratio

import ToySolver.Data.OrdRel
import ToySolver.Data.FOL.Formula
import ToySolver.Data.IntVar

-- ---------------------------------------------------------------------------

-- | Arithmetic expressions
data Expr r
  = Const r
  | Var Var
  | Expr r :+: Expr r
  | Expr r :*: Expr r
  | Expr r :/: Expr r
  deriving (Eq, Ord, Show)

instance Num r => Num (Expr r) where
  a + b = a :+: b
  a * b = a :*: b
  a - b = a + negate b
  negate a = Const (-1) :*: a
  abs a = a
  signum _ = 1
  fromInteger = Const . fromInteger

instance Fractional r => Fractional (Expr r) where
  a / b = a :/: b
  fromRational x = fromInteger (numerator x) / fromInteger (denominator x)

instance Functor Expr where
  fmap f = g
    where
      g (Const c) = Const (f c)
      g (Var v)   = Var v
      g (a :+: b) = g a :+: g b
      g (a :*: b) = g a :*: g b
      g (a :/: b) = g a :/: g b

instance Variables (Expr r) where
  vars (Const _) = IS.empty
  vars (Var v)   = IS.singleton v
  vars (a :+: b) = vars a `IS.union` vars b
  vars (a :*: b) = vars a `IS.union` vars b
  vars (a :/: b) = vars a `IS.union` vars b

-- | single variable expression
var :: Var -> Expr r
var = Var

-- | evaluate an 'Expr' with respect to a 'Model'
evalExpr :: Fractional r => Model r -> Expr r -> r
evalExpr m = f
  where
    f (Const x) = x
    f (Var v) = m IM.! v
    f (a :+: b) = f a + f b
    f (a :*: b) = f a * f b
    f (a :/: b) = f a / f b

instance Fractional r => Eval (Model r) (Expr r) r where
  eval = evalExpr

-- ---------------------------------------------------------------------------

-- | Atomic formula
type Atom c = OrdRel (Expr c)

evalAtom :: (Real r, Fractional r) => Model r -> Atom r -> Bool
evalAtom m (OrdRel a op b) = evalOp op (evalExpr m a) (evalExpr m b)

instance IsEqRel (Expr c) (Formula (Atom c)) where
  a .==. b = Atom (a .==. b)
  a ./=. b = Atom (a ./=. b)

instance IsOrdRel (Expr c) (Formula (Atom c)) where
  ordRel op a b = Atom (ordRel op a b)

-- ---------------------------------------------------------------------------

-- | results of satisfiability checking
data SatResult r = Unknown | Unsat | Sat (Model r)
  deriving (Show, Eq, Ord)

-- ---------------------------------------------------------------------------
