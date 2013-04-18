{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.FOL.Arith
-- Copyright   :  (c) Masahiro Sakai 2011-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (FlexibleInstances, MultiParamTypeClasses)
--
-- Arithmetic language (not limited to linear ones).
-- 
-----------------------------------------------------------------------------
module Data.FOL.Arith
  (
  -- * Arithmetic expressions
    Expr (..)
  , var
  , evalExpr

  -- * Atomic formula
  , module Data.ArithRel
  , Atom (..)
  , evalAtom

  -- * Arithmetic formula
  , module Data.FOL.Formula  

  -- * Misc
  , SatResult (..)
  ) where

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.Ratio

import Data.ArithRel
import Data.FOL.Formula
import Data.Var

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

-- ---------------------------------------------------------------------------

-- | Atomic formula
type Atom c = Rel (Expr c)

evalAtom :: (Real r, Fractional r) => Model r -> Atom r -> Bool
evalAtom m (Rel a op b) = evalOp op (evalExpr m a) (evalExpr m b)

instance IsRel (Expr c) (Formula (Atom c)) where
  rel op a b = Atom $ rel op a b

-- ---------------------------------------------------------------------------

-- | results of satisfiability checking
data SatResult r = Unknown | Unsat | Sat (Model r)
  deriving (Show, Eq, Ord)

-- ---------------------------------------------------------------------------
