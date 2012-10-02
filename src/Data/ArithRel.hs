{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.ArithRel
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (MultiParamTypeClasses, FunctionalDependencies)
--
-- Arithmetic relations
-- 
-----------------------------------------------------------------------------
module Data.ArithRel
  (
  -- * Relational operators
    RelOp (..)
  , Rel (..)
  , (.<.), (.<=.), (.>=.), (.>.), (.==.), (./=.)
  , flipOp
  , negOp
  , showOp
  ) where

infix 4 .<., .<=., .>=., .>., .==., ./=.

-- | relational operators
data RelOp = Lt | Le | Ge | Gt | Eql | NEq
    deriving (Show, Eq, Ord)

-- | type class for constructing relational formula
class Rel e r | r -> e where
  rel :: RelOp -> e -> e -> r

-- | constructing relational formula
(.<.) :: Rel e r => e -> e -> r
a .<. b  = rel Lt  a b

-- | constructing relational formula
(.<=.) :: Rel e r => e -> e -> r
a .<=. b = rel Le  a b

-- | constructing relational formula
(.>.) :: Rel e r => e -> e -> r
a .>. b  = rel Gt  a b

-- | constructing relational formula
(.>=.) :: Rel e r => e -> e -> r
a .>=. b = rel Ge  a b

-- | constructing relational formula
(.==.) :: Rel e r => e -> e -> r
a .==. b = rel Eql a b

-- | constructing relational formula
(./=.) :: Rel e r => e -> e -> r
a ./=. b = rel NEq a b

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

