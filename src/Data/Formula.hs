{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Formula
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (MultiParamTypeClasses, FlexibleInstances)
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
type Atom c = Rel (Expr c)

-- ---------------------------------------------------------------------------

-- | formulas of first order logic
data Formula a
    = T
    | F
    | Atom a
    | And (Formula a) (Formula a)
    | Or (Formula a) (Formula a)
    | Not (Formula a)
    | Imply (Formula a) (Formula a)
    | Equiv (Formula a) (Formula a)
    | Forall Var (Formula a)
    | Exists Var (Formula a)
    deriving (Show, Eq, Ord)

instance Variables a => Variables (Formula a) where
  vars T = IS.empty
  vars F = IS.empty
  vars (Atom a) = vars a
  vars (And a b) = vars a `IS.union` vars b
  vars (Or a b) = vars a `IS.union` vars b
  vars (Not a) = vars a
  vars (Imply a b) = vars a `IS.union` vars b
  vars (Equiv a b) = vars a `IS.union` vars b
  vars (Forall v a) = IS.delete v (vars a)
  vars (Exists v a) = IS.delete v (vars a)

instance Complement (Formula a) where
  notB = Not

instance Lattice (Formula c) where
  top    = T
  bottom = F
  meet   = And
  join   = Or

instance Boolean (Formula c) where
  (.=>.)  = Imply
  (.<=>.) = Equiv

instance IsRel (Expr c) (Formula (Atom c)) where
  rel op a b = Atom $ rel op a b

-- | convert a formula into negation normal form
pushNot :: Complement a => Formula a -> Formula a
pushNot T = F
pushNot F = T
pushNot (Atom a) = Atom $ notB a
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
