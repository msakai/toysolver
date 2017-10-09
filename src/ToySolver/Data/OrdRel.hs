{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.OrdRel
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances)
--
-- Ordering relations
-- 
-----------------------------------------------------------------------------
module ToySolver.Data.OrdRel
  (
  -- * Relational operators
    RelOp (..)
  , flipOp
  , negOp
  , showOp
  , evalOp

  -- * Relation
  , OrdRel (..)
  , fromOrdRel

  -- * DSL
  , IsEqRel (..)
  , IsOrdRel (..)
  ) where

import qualified Data.IntSet as IS

import ToySolver.Data.Boolean
import ToySolver.Data.IntVar

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
class IsEqRel e r | r -> e where
  (.==.) :: e -> e -> r
  (./=.) :: e -> e -> r

-- | type class for constructing relational formula
class IsEqRel e r => IsOrdRel e r | r -> e where
  (.<.), (.<=.), (.>.), (.>=.) :: e -> e -> r
  ordRel :: RelOp -> e -> e -> r

  a .<. b  = ordRel Lt a b
  a .<=. b = ordRel Le a b
  a .>. b  = ordRel Gt a b
  a .>=. b = ordRel Ge a b

  ordRel Lt a b  = a .<. b
  ordRel Gt a b  = a .>. b
  ordRel Le a b  = a .<=. b
  ordRel Ge a b  = a .>=. b
  ordRel Eql a b = a .==. b
  ordRel NEq a b = a ./=. b

  {-# MINIMAL ((.<.), (.<=.), (.>.), (.>=.)) | ordRel #-}

-- ---------------------------------------------------------------------------

-- | Atomic formula
data OrdRel e = OrdRel e RelOp e
    deriving (Show, Eq, Ord)

instance Complement (OrdRel c) where
  notB (OrdRel lhs op rhs) = OrdRel lhs (negOp op) rhs

instance IsEqRel e (OrdRel e) where
  (.==.) = ordRel Eql
  (./=.) = ordRel NEq

instance IsOrdRel e (OrdRel e) where
  ordRel op a b = OrdRel a op b

instance Variables e => Variables (OrdRel e) where
  vars (OrdRel a _ b) = vars a `IS.union` vars b

instance Functor OrdRel where
  fmap f (OrdRel a op b) = OrdRel (f a) op (f b)

fromOrdRel :: IsOrdRel e r => OrdRel e -> r
fromOrdRel (OrdRel a op b) = ordRel op a b

-- ---------------------------------------------------------------------------

instance (Eval m e a, Ord a) => Eval m (OrdRel e) Bool where
  eval m (OrdRel lhs op rhs) = evalOp op (eval m lhs) (eval m rhs)
