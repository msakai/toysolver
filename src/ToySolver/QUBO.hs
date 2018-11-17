{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.QUBO
-- Copyright   :  (c) Masahiro Sakai 2018
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
-- 
-----------------------------------------------------------------------------
module ToySolver.QUBO
  ( Problem (..)
  , Solution (..)
  , eval
  ) where

import Control.Monad
import Data.Array.Unboxed
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

data Problem a
  = Problem
  { quboNumVars :: !Int
    -- ^ Number of variables N. Variables are numbered from 0 to N-1.
  , quboMatrix :: IntMap (IntMap a)
    -- ^ Upper triangular matrix
  }
  deriving (Eq, Show)

type Solution = UArray Int Bool

eval :: Num a => Solution -> Problem a -> a
eval sol prob = sum $ do
  (x1, row) <- IntMap.toList $ quboMatrix prob
  guard $ sol ! x1
  (x2, c) <- IntMap.toList row
  guard $ sol ! x2
  return c
