{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.QUBO
-- Copyright   :  (c) Masahiro Sakai 2018
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
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
import Data.ByteString.Builder
import Data.ByteString.Builder.Scientific
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
#if !MIN_VERSION_base(4,11,0)
import Data.Monoid
#endif
import Data.Scientific
import ToySolver.FileFormat.Base

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

parseProblem :: (BS.ByteString -> a) -> BS.ByteString -> Either String (Problem a)
parseProblem f s =
  case BS.words l of
    ["p", filetype, topology, maxNodes, _nNodes, _nCouplers] ->
      if filetype /= "qubo" then
        Left $ "unknown filetype: " ++ BS.unpack filetype
      else if topology /= "0" && topology /= "unconstrained" then
        Left $ "unknown topology: " ++ BS.unpack topology
      else
        Right $ Problem
        { quboNumVars = read (BS.unpack maxNodes)
        , quboMatrix =
            IntMap.unionsWith IntMap.union $ do
              l <- ls
              case BS.words l of
                [i, j, v] -> return $ IntMap.singleton (read (BS.unpack i)) $ IntMap.singleton (read (BS.unpack j)) $ f v
        }
  where
    (l:ls) = filter (not . isCommentBS) (BS.lines s)

    isCommentBS :: BS.ByteString -> Bool
    isCommentBS s =
      case BS.uncons s of
        Just ('c',_) ->  True
        _ -> False

renderProblem :: (a -> Builder) -> Problem a -> Builder
renderProblem f prob = header
    <> mconcat [ intDec i <> char7 ' ' <> intDec i <> char7 ' ' <> f val <> char7 '\n'
               | (i,val) <- IntMap.toList nodes
               ]
    <> mconcat [intDec i <> char7 ' ' <> intDec j <> char7 ' ' <> f val <> char7 '\n'
               | (i,row) <- IntMap.toList couplers, (j,val) <- IntMap.toList row
               ]
  where
    nodes = IntMap.mapMaybeWithKey IntMap.lookup (quboMatrix prob)
    nNodes = IntMap.size nodes
    couplers = IntMap.mapWithKey IntMap.delete (quboMatrix prob)
    nCouplers = sum [IntMap.size row | row <- IntMap.elems couplers]
    header = mconcat
      ["p qubo 0 "
      , intDec (quboNumVars prob), char7 ' '
      , intDec nNodes, char7 ' '
      , intDec nCouplers, char7 '\n'
      ]

instance FileFormat (Problem Scientific) where
  parse = parseProblem (read . BS.unpack)
  render = renderProblem scientificBuilder


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
