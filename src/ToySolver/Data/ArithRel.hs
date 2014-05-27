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
  , Rel (..)

  -- * DSL
  , IsRel (..)
  , (.<.), (.<=.), (.>=.), (.>.), (.==.), (./=.)
  ) where

import qualified Data.IntSet as IS

import ToySolver.Algebra.Lattice.Boolean (Complement (..))
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
class IsRel e r | r -> e where
  rel :: RelOp -> e -> e -> r

-- | constructing relational formula
(.<.) :: IsRel e r => e -> e -> r
a .<. b  = rel Lt  a b

-- | constructing relational formula
(.<=.) :: IsRel e r => e -> e -> r
a .<=. b = rel Le  a b

-- | constructing relational formula
(.>.) :: IsRel e r => e -> e -> r
a .>. b  = rel Gt  a b

-- | constructing relational formula
(.>=.) :: IsRel e r => e -> e -> r
a .>=. b = rel Ge  a b

-- | constructing relational formula
(.==.) :: IsRel e r => e -> e -> r
a .==. b = rel Eql a b

-- | constructing relational formula
(./=.) :: IsRel e r => e -> e -> r
a ./=. b = rel NEq a b

-- ---------------------------------------------------------------------------

-- | Atomic formula
data Rel e = Rel e RelOp e
    deriving (Show, Eq, Ord)

instance Complement (Rel c) where
  notB (Rel lhs op rhs) = Rel lhs (negOp op) rhs

instance IsRel e (Rel e) where
  rel op a b = Rel a op b

instance Variables e => Variables (Rel e) where
  vars (Rel a _ b) = vars a `IS.union` vars b

instance Functor Rel where
  fmap f (Rel a op b) = Rel (f a) op (f b)

-- ---------------------------------------------------------------------------
