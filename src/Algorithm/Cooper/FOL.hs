{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.Cooper.FOL
-- Copyright   :  (c) Masahiro Sakai 2011-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
-- 
-----------------------------------------------------------------------------
module Algorithm.Cooper.FOL
    ( eliminateQuantifiers
    , solveFormula
    ) where

import Control.Monad

import Algebra.Lattice.Boolean

import Data.ArithRel
import qualified Data.FOL.Arith as FOL
import qualified Data.LA.FOL as LAFOL
import Data.Var

import Algorithm.Cooper.Core

-- | eliminate quantifiers and returns equivalent quantifier-free formula.
eliminateQuantifiers :: FOL.Formula (FOL.Atom Rational) -> Maybe QFFormula
eliminateQuantifiers = f
  where
    f FOL.T = return T'
    f FOL.F = return F'
    f (FOL.Atom (Rel a op b)) = do
       a' <- LAFOL.fromFOLExpr a
       b' <- LAFOL.fromFOLExpr b
       return $ fromLAAtom (Rel a' op b')
    f (FOL.And a b) = liftM2 (.&&.) (f a) (f b)
    f (FOL.Or a b) = liftM2 (.||.) (f a) (f b)
    f (FOL.Not a) = f (FOL.pushNot a)
    f (FOL.Imply a b) = f $ FOL.Or (FOL.Not a) b
    f (FOL.Equiv a b) = f $ FOL.And (FOL.Imply a b) (FOL.Imply b a)
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
