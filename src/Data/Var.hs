-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Var
-- Copyright   :  (c) Masahiro Sakai 2011-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
-- 
-----------------------------------------------------------------------------
module Data.Var
  ( Var
  , VarSet
  , VarMap
  , Variables (..)
  , Model
  ) where

import Data.IntMap (IntMap)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Ratio

-- ---------------------------------------------------------------------------

-- | Variables are represented as non-negative integers
type Var = Int

-- | Set of variables
type VarSet = IntSet

-- | Map from variables
type VarMap = IntMap

-- | collecting free variables
class Variables a where
  vars :: a -> VarSet

instance Variables a => Variables [a] where
  vars = IntSet.unions . map vars

-- | A @Model@ is a map from variables to values.
type Model r = VarMap r

-- ---------------------------------------------------------------------------
