-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Expr
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Arithmetic expressions (not limited to linear ones).
-- 
-----------------------------------------------------------------------------
module Data.Expr
  ( Var
  , VarSet
  , VarMap
  , Variables (..)
  , Model
  , Expr (..)
  , var
  , eval

  -- FIXME: どこか違うモジュールへ?
  , SatResult (..)
  , OptResult (..)
  ) where

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.Ratio

-- ---------------------------------------------------------------------------

-- | Variables are represented as non-negative integers
type Var = Int

-- | Set of variables
type VarSet = IS.IntSet

-- | Map from variables
type VarMap = IM.IntMap

-- | collecting free variables
class Variables a where
  vars :: a -> VarSet

instance Variables a => Variables [a] where
  vars = IS.unions . map vars

-- | A @Model@ is a map from variables to values.
type Model r = VarMap r

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
eval :: Fractional r => Model r -> Expr r -> r
eval m = f
  where
    f (Const x) = x
    f (Var v) = m IM.! v
    f (a :+: b) = f a + f b
    f (a :*: b) = f a * f b
    f (a :/: b) = f a / f b

-- ---------------------------------------------------------------------------

-- | results of satisfiability checking
data SatResult r = Unknown | Unsat | Sat (Model r)
  deriving (Show, Eq, Ord)

-- | results of optimization
data OptResult r = OptUnknown | OptUnsat | Unbounded | Optimum r (Model r)
  deriving (Show, Eq, Ord)

-- ---------------------------------------------------------------------------
