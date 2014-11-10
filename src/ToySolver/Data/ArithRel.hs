{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.ArithRel
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies)
--
-- Arithmetic relations
-- 
-----------------------------------------------------------------------------
module ToySolver.Data.ArithRel
  (
  -- * Relational operators
    RelOp (..)
  , flipOp
  , negOp
  , showOp
  , evalOp

  -- * Relation
  , ArithRel (..)

  -- * DSL
  , IsArithRel (..)
  , (.<.), (.<=.), (.>=.), (.>.), (.==.), (./=.)
  ) where

import qualified Data.IntSet as IS

import ToySolver.Data.Boolean
import ToySolver.Data.Var

infix 4 .<., .<=., .>=., .>., .==., ./=.

-- ---------------------------------------------------------------------------

-- | relational operators
data RelOp = Lt | Le | Ge | Gt | Eql | NEq
    deriving (Show, Eq, Ord)


-- | flipping relational operator
--
-- @rel (flipOp op) a b@ is equivalent to @rel op b a@
flipOp :: RelOp -> RelOp 
flipOp Le = Ge
flipOp Ge = Le
flipOp Lt = Gt
flipOp Gt = Lt
flipOp Eql = Eql
flipOp NEq = NEq

-- | negating relational operator
--
-- @rel (negOp op) a b@ is equivalent to @notB (rel op a b)@
negOp :: RelOp -> RelOp
negOp Lt = Ge
negOp Le = Gt
negOp Ge = Lt
negOp Gt = Le
negOp Eql = NEq
negOp NEq = Eql

-- | operator symbol
showOp :: RelOp -> String
showOp Lt = "<"
showOp Le = "<="
showOp Ge = ">="
showOp Gt = ">"
showOp Eql = "="
showOp NEq = "/="

-- | evaluate an operator into a comparision function
evalOp :: Ord a => RelOp -> a -> a -> Bool
evalOp Lt = (<)
evalOp Le = (<=)
evalOp Ge = (>=)
evalOp Gt = (>)
evalOp Eql = (==)
evalOp NEq = (/=)

-- ---------------------------------------------------------------------------

-- | type class for constructing relational formula
class IsArithRel e r | r -> e where
  arithRel :: RelOp -> e -> e -> r

-- | constructing relational formula
(.<.) :: IsArithRel e r => e -> e -> r
a .<. b  = arithRel Lt a b

-- | constructing relational formula
(.<=.) :: IsArithRel e r => e -> e -> r
a .<=. b = arithRel Le a b

-- | constructing relational formula
(.>.) :: IsArithRel e r => e -> e -> r
a .>. b  = arithRel Gt a b

-- | constructing relational formula
(.>=.) :: IsArithRel e r => e -> e -> r
a .>=. b = arithRel Ge a b

-- | constructing relational formula
(.==.) :: IsArithRel e r => e -> e -> r
a .==. b = arithRel Eql a b

-- | constructing relational formula
(./=.) :: IsArithRel e r => e -> e -> r
a ./=. b = arithRel NEq a b

-- ---------------------------------------------------------------------------

-- | Atomic formula
data ArithRel e = ArithRel e RelOp e
    deriving (Show, Eq, Ord)

instance Complement (ArithRel c) where
  notB (ArithRel lhs op rhs) = ArithRel lhs (negOp op) rhs

instance IsArithRel e (ArithRel e) where
  arithRel op a b = ArithRel a op b

instance Variables e => Variables (ArithRel e) where
  vars (ArithRel a _ b) = vars a `IS.union` vars b

instance Functor ArithRel where
  fmap f (ArithRel a op b) = ArithRel (f a) op (f b)

-- ---------------------------------------------------------------------------
