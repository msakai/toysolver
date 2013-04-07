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

import Data.Lattice

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
