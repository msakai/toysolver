-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.DNF
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
module ToySolver.Data.DNF
  ( DNF (..)
  ) where

import ToySolver.Data.Boolean

-- | Disjunctive normal form
newtype DNF lit
  = DNF
  { unDNF :: [[lit]] -- ^ list of conjunction of literals
  } deriving (Show)

instance Complement lit => Complement (DNF lit) where
  notB (DNF xs) = DNF . sequence . map (map notB) $ xs

instance MonotoneBoolean (DNF lit) where
  true  = DNF [[]]
  false = DNF []
  DNF xs .||. DNF ys = DNF (xs++ys)
  DNF xs .&&. DNF ys = DNF [x++y | x<-xs, y<-ys]

instance Complement lit => Boolean (DNF lit)

