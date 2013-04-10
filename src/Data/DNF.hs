-----------------------------------------------------------------------------
-- |
-- Module      :  Data.DNF
-- Copyright   :  (c) Masahiro Sakai 2011-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Disjunctive Normal Form
-- 
-----------------------------------------------------------------------------
module Data.DNF
  ( DNF (..)
  ) where

import Algebra.Lattice
import Algebra.Lattice.Boolean

-- | Disjunctive normal form
newtype DNF lit
  = DNF
  { unDNF :: [[lit]] -- ^ list of conjunction of literals
  } deriving (Show)

instance Complement lit => Complement (DNF lit) where
  notB (DNF xs) = DNF . sequence . map (map notB) $ xs

instance JoinSemiLattice (DNF lit) where
  DNF xs `join` DNF ys = DNF (xs++ys)

instance MeetSemiLattice (DNF lit) where
  DNF xs `meet` DNF ys = DNF [x++y | x<-xs, y<-ys]

instance Lattice (DNF lit)

instance BoundedJoinSemiLattice (DNF lit) where
  bottom = DNF []

instance BoundedMeetSemiLattice (DNF lit) where
  top = DNF [[]]

instance BoundedLattice (DNF lit)

instance Complement lit => Boolean (DNF lit)
