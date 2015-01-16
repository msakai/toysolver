{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.PBFile.Types
-- Copyright   :  (c) Masahiro Sakai 2011-2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Portability :  non-portable (BangPatterns)
--
-- A parser library for .opb file and .wbo files used by PB Competition.
-- 
-- References:
--
-- * Input/Output Format and Solver Requirements for the Competitions of
--   Pseudo-Boolean Solvers
--   <http://www.cril.univ-artois.fr/PB11/format.pdf>
--
-----------------------------------------------------------------------------

module ToySolver.Text.PBFile.Types
  (
  -- * Abstract Syntax
    Formula (..)
  , Constraint
  , Op (..)
  , SoftFormula (..)
  , SoftConstraint
  , Sum
  , WeightedTerm
  , Term
  , Lit
  , Var

  -- * Internal utilities
  , pbComputeNumVars
  , wboComputeNumVars
  ) where

import Data.Maybe

-- | Pair of /objective function/ and a list of constraints.
data Formula
  = Formula
  { pbObjectiveFunction :: Maybe Sum
  , pbConstraints :: [Constraint]
  , pbNumVars :: !Int
  , pbNumConstraints :: !Int
  }
  deriving (Eq, Ord, Show)

-- | Lhs, relational operator and rhs.
type Constraint = (Sum, Op, Integer)

-- | Relational operators
data Op
  = Ge -- ^ /greater than or equal/
  | Eq -- ^ /equal/
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | A pair of /top cost/ and a list of soft constraints.
data SoftFormula
  = SoftFormula
  { wboTopCost :: Maybe Integer
  , wboConstraints :: [SoftConstraint]
  , wboNumVars :: !Int
  , wboNumConstraints :: !Int
  }
  deriving (Eq, Ord, Show)

-- | A pair of weight and constraint.
type SoftConstraint = (Maybe Integer, Constraint)

-- | Sum of 'WeightedTerm'
type Sum = [WeightedTerm]

-- | Coefficient and 'Term'
type WeightedTerm = (Integer, Term)

-- | List of variables interpreted as products
type Term = [Lit]

-- | Positive (resp. negative) literals are represented as positive (resp. negative) integers.
type Lit = Int

-- | Variable are repserented positive integers.
type Var = Int

pbComputeNumVars :: Maybe Sum -> [Constraint] -> Int
pbComputeNumVars obj cs = maximum (0 : vs)
  where
    vs = do
      s <- maybeToList obj ++ [s | (s,_,_) <- cs]
      (_, tm) <- s
      lit <- tm
      return $ abs lit

wboComputeNumVars :: [SoftConstraint] -> Int
wboComputeNumVars cs = maximum (0 : vs)
  where
    vs = do
      s <- [s | (_, (s,_,_)) <- cs]
      (_, tm) <- s
      lit <- tm
      return $ abs lit
