module Expr
  ( Var
  , VarSet
  , VarMap
  , Variables (..)
  , Model
  , Expr (..)
  , var
  , eval
  ) where

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.Ratio

-- | Variables are represented as non-negative integers
type Var = Int
type VarSet = IS.IntSet
type VarMap = IM.IntMap

class Variables a where
  vars :: a -> VarSet

instance Variables a => Variables [a] where
  vars = IS.unions . map vars

type Model r = VarMap r

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

instance Variables (Expr r) where
  vars (Const _) = IS.empty
  vars (Var v) = IS.singleton v
  vars (a :+: b) = vars a `IS.union` vars b
  vars (a :*: b) = vars a `IS.union` vars b
  vars (a :/: b) = vars a `IS.union` vars b

var :: Var -> Expr r
var = Var

eval :: Fractional r => Model r -> Expr r -> r
eval m = f
  where
    f (Const x) = x
    f (Var v) = m IM.! v
    f (a :+: b) = f a + f b
    f (a :*: b) = f a * f b
    f (a :/: b) = f a / f b
