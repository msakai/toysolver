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
  ( -- * QUBO (quadratic unconstrained boolean optimization)
    Problem (..)
  , Solution (..)
  , eval

    -- * Ising Model
  , IsingModel (..)
  , evalIsingModel
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


data IsingModel a
  = IsingModel
  { isingNumVars :: !Int
    -- ^ Number of variables N. Variables are numbered from 0 to N-1.
  , isingInteraction :: IntMap (IntMap a)
    -- ^ Interaction \(J_{i,j}\) with \(i < j\).
  , isingExternalMagneticField :: IntMap a
    -- ^ External magnetic field \(h_j\).
  }
  deriving (Eq, Show)

-- | +1 is represented as True and -1 is represented as False.
evalIsingModel :: Num a => Solution -> IsingModel a -> a
evalIsingModel sol m
  = sum [ jj_ij * sigma i *  sigma j
        | (i, row) <- IntMap.toList $ isingInteraction m, (j, jj_ij) <- IntMap.toList row
        ]
  + sum [ h_i * sigma i | (i, h_i) <- IntMap.toList $ isingExternalMagneticField m ]
  where
    sigma i = if sol ! i then 1 else -1
