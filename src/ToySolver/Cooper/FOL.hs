{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Cooper.FOL
-- Copyright   :  (c) Masahiro Sakai 2011-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
-- 
-----------------------------------------------------------------------------
module ToySolver.Cooper.FOL
    ( eliminateQuantifiers
    , solveFormula
    ) where

import Control.Monad

import ToySolver.Data.ArithRel
import ToySolver.Data.Boolean
import qualified ToySolver.Data.FOL.Arith as FOL
import qualified ToySolver.Data.LA.FOL as LAFOL
import ToySolver.Data.Var
import ToySolver.Cooper.Core

-- | eliminate quantifiers and returns equivalent quantifier-free formula.
eliminateQuantifiers :: FOL.Formula (FOL.Atom Rational) -> Maybe QFFormula
eliminateQuantifiers = f
  where
    f FOL.T = return true
    f FOL.F = return false
    f (FOL.Atom (ArithRel a op b)) = do
       a' <- LAFOL.fromFOLExpr a
       b' <- LAFOL.fromFOLExpr b
       return $ fromLAAtom (ArithRel a' op b')
    f (FOL.And a b) = liftM2 (.&&.) (f a) (f b)
    f (FOL.Or a b) = liftM2 (.||.) (f a) (f b)
    f (FOL.Not a) = liftM notB (f a)
    f (FOL.Imply a b) = liftM2 (.=>.) (f a) (f b)
    f (FOL.Equiv a b) = liftM2 (.<=>.) (f a) (f b)
    f (FOL.Forall x body) = liftM notB $ f $ FOL.Exists x $ FOL.Not body
    f (FOL.Exists x body) = liftM (fst . project x) (f body)

solveFormula :: VarSet -> FOL.Formula (FOL.Atom Rational) -> FOL.SatResult Integer
solveFormula vs formula =
  case eliminateQuantifiers formula of
    Nothing -> FOL.Unknown
    Just formula' ->
       case solveQFFormula vs formula' of
         Nothing -> FOL.Unsat
         Just m -> FOL.Sat m
