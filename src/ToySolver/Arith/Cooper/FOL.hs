{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Arith.Cooper.FOL
-- Copyright   :  (c) Masahiro Sakai 2011-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
-- 
-----------------------------------------------------------------------------
module ToySolver.Arith.Cooper.FOL
    ( eliminateQuantifiers
    , solveFormula
    ) where

import Control.Monad

import ToySolver.Data.OrdRel
import ToySolver.Data.Boolean
import qualified ToySolver.Data.FOL.Arith as FOL
import qualified ToySolver.Data.LA.FOL as LAFOL
import ToySolver.Data.Var
import ToySolver.Arith.Cooper.Base

-- | Eliminate quantifiers and returns equivalent quantifier-free formula.
--
-- @'eliminateQuantifiers' φ@ returns @(ψ, lift)@ such that:
--
-- * ψ is a quantifier-free formula and @LIA ⊢ ∀y1, …, yn. φ ↔ ψ@ where @{y1, …, yn} = FV(φ) ⊇ FV(ψ)@, and
--
-- * if @M ⊧_LIA ψ@ then @lift M ⊧_LIA φ@.
--
-- φ may or may not be a closed formula.
--
eliminateQuantifiers :: FOL.Formula (FOL.Atom Rational) -> Maybe QFFormula
eliminateQuantifiers = f
  where
    f FOL.T = return true
    f FOL.F = return false
    f (FOL.Atom (OrdRel a op b)) = do
       a' <- LAFOL.fromFOLExpr a
       b' <- LAFOL.fromFOLExpr b
       return $ fromLAAtom (OrdRel a' op b')
    f (FOL.And a b) = liftM2 (.&&.) (f a) (f b)
    f (FOL.Or a b) = liftM2 (.||.) (f a) (f b)
    f (FOL.Not a) = liftM notB (f a)
    f (FOL.Imply a b) = liftM2 (.=>.) (f a) (f b)
    f (FOL.Equiv a b) = liftM2 (.<=>.) (f a) (f b)
    f (FOL.Forall x body) = liftM notB $ f $ FOL.Exists x $ FOL.Not body
    f (FOL.Exists x body) = liftM (fst . project x) (f body)

-- | @'solveFormula' {x1,…,xm} φ@
--
-- * returns @'Sat' M@ such that @M ⊧_LIA φ@ when such @M@ exists,
--
-- * returns @'Unsat'@ when such @M@ does not exists, and
--
-- * returns @'Unknown'@ when @φ@ is beyond LIA.
-- 
solveFormula :: VarSet -> FOL.Formula (FOL.Atom Rational) -> FOL.SatResult Integer
solveFormula vs formula =
  case eliminateQuantifiers formula of
    Nothing -> FOL.Unknown
    Just formula' ->
       case solveQFFormula vs formula' of
         Nothing -> FOL.Unsat
         Just m -> FOL.Sat m
