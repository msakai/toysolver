{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Formula
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (MultiParamTypeClasses, FunctionalDependencies)
--
-- Formula of first order logic.
-- 
-----------------------------------------------------------------------------
module Data.Formula
  (
  -- * Overloaded operations for formula.
    module Data.Lattice

  -- * Relational operators
  , module Data.ArithRel

  -- * Concrete formula
  , Atom (..)
  , Formula (..)
  , pushNot
  , DNF (..)
  ) where

import qualified Data.IntSet as IS
import Data.Expr
import Data.Lattice
import Data.ArithRel

-- ---------------------------------------------------------------------------

-- | Atomic formula
data Atom c = Rel (Expr c) RelOp (Expr c)
    deriving (Show, Eq, Ord)

instance Complement (Atom c) where
  notB (Rel lhs op rhs) = Rel lhs (negOp op) rhs

instance Variables (Atom c) where
  vars (Rel a _ b) = vars a `IS.union` vars b

instance Rel (Expr c) (Atom c) where
  rel op a b = Rel a op b

-- ---------------------------------------------------------------------------

-- | formulas of first order logic
data Formula c
    = T
    | F
    | Atom (Atom c)
    | And (Formula c) (Formula c)
    | Or (Formula c) (Formula c)
    | Not (Formula c)
    | Imply (Formula c) (Formula c)
    | Equiv (Formula c) (Formula c)
    | Forall Var (Formula c)
    | Exists Var (Formula c)
    deriving (Show, Eq, Ord)

instance Variables (Formula c) where
  vars T = IS.empty
  vars F = IS.empty
  vars (Atom atom) = vars atom
  vars (And a b) = vars a `IS.union` vars b
  vars (Or a b) = vars a `IS.union` vars b
  vars (Not a) = vars a
  vars (Imply a b) = vars a `IS.union` vars b
  vars (Equiv a b) = vars a `IS.union` vars b
  vars (Forall v a) = IS.delete v (vars a)
  vars (Exists v a) = IS.delete v (vars a)

instance Complement (Formula c) where
  notB = Not

instance Lattice (Formula c) where
  top    = T
  bottom = F
  meet   = And
  join   = Or

instance Boolean (Formula c) where
  (.=>.)  = Imply
  (.<=>.) = Equiv

instance Rel (Expr c) (Formula c) where
  rel op a b = Atom $ rel op a b

-- | convert a formula into negation normal form
pushNot :: Formula c -> Formula c
pushNot T = F
pushNot F = T
pushNot (Atom (Rel a op b)) = Atom $ Rel a (negOp op) b
pushNot (And a b) = Or (pushNot a) (pushNot b)
pushNot (Or a b) = And (pushNot a) (pushNot b)
pushNot (Not a) = a
pushNot (Imply a b) = And a (pushNot b)
pushNot (Equiv a b) = Or (And a (pushNot b)) (And b (pushNot a))
pushNot (Forall v a) = Exists v (pushNot a)
pushNot (Exists v a) = Forall v (pushNot a)

-- | Disjunctive normal form
newtype DNF lit
  = DNF
  { unDNF :: [[lit]] -- ^ list of conjunction of literals
  } deriving (Show)

instance Complement lit => Complement (DNF lit) where
  notB (DNF xs) = DNF . sequence . map (map notB) $ xs

instance Complement lit => Lattice (DNF lit) where
  top    = DNF [[]]
  bottom = DNF []
  DNF xs `meet` DNF ys = DNF [x++y | x<-xs, y<-ys]
  DNF xs `join` DNF ys = DNF (xs++ys)

instance Complement lit => Boolean (DNF lit)
