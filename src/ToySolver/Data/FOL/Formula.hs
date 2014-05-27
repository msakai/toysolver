-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.FOL.Formula
-- Copyright   :  (c) Masahiro Sakai 2011-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Formula of first order logic.
-- 
-----------------------------------------------------------------------------
module ToySolver.Data.FOL.Formula
  (
  -- * Overloaded operations for formula.
    module ToySolver.Algebra.Lattice.Boolean

  -- * Concrete formula
  , Formula (..)
  , pushNot
  ) where

import Algebra.Lattice
import qualified Data.IntSet as IS

import ToySolver.Algebra.Lattice.Boolean
import ToySolver.Data.Var

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

instance JoinSemiLattice (Formula c) where
  join = Or

instance MeetSemiLattice (Formula c) where
  meet = And

instance Lattice (Formula c)

instance BoundedJoinSemiLattice (Formula c) where
  bottom = F

instance BoundedMeetSemiLattice (Formula c) where
  top = T

instance BoundedLattice (Formula c)

instance Boolean (Formula c) where
  (.=>.)  = Imply
  (.<=>.) = Equiv

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
