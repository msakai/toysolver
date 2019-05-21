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
  , Solution
  , eval

    -- * Ising Model
  , IsingModel (..)
  , evalIsingModel
  ) where

import Control.Monad
import Data.Array.Unboxed
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

-- | QUBO (quadratic unconstrained boolean optimization) problem.
--
-- Minimize \(\sum_{i\le j} Q_{i,j} x_i x_j\) where \(x_i \in \{0,1\}\) for \(i \in \{0 \ldots N-1\}\).
--
-- In the `Solution` type. 0 and 1 are represented as @False@ and @True@ respectively.
data Problem a
  = Problem
  { quboNumVars :: !Int
    -- ^ Number of variables N. Variables are numbered from 0 to N-1.
  , quboMatrix :: IntMap (IntMap a)
    -- ^ Upper triangular matrix Q
  }
  deriving (Eq, Show)

instance Functor Problem where
  fmap f prob =
    Problem
    { quboNumVars = quboNumVars prob
    , quboMatrix = fmap (fmap f) (quboMatrix prob)
    }

type Solution = UArray Int Bool

eval :: Num a => Solution -> Problem a -> a
eval sol prob = sum $ do
  (x1, row) <- IntMap.toList $ quboMatrix prob
  guard $ sol ! x1
  (x2, c) <- IntMap.toList row
  guard $ sol ! x2
  return c


-- | Ising model.
--
-- Minimize \(\sum_{i<j} J_{i,j} \sigma_i \sigma_j + \sum_i h_i \sigma_i\) where \(\sigma_i \in \{-1,+1\}\) for \(i \in \{0 \ldots N-1\}\).
--
-- In the `Solution` type. -1 and +1 are represented as @False@ and @True@ respectively.
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

evalIsingModel :: Num a => Solution -> IsingModel a -> a
evalIsingModel sol m
  = sum [ jj_ij * sigma i *  sigma j
        | (i, row) <- IntMap.toList $ isingInteraction m, (j, jj_ij) <- IntMap.toList row
        ]
  + sum [ h_i * sigma i | (i, h_i) <- IntMap.toList $ isingExternalMagneticField m ]
  where
    sigma i = if sol ! i then 1 else -1
