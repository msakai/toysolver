-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.MaxCut
-- Copyright   :  (c) Masahiro Sakai 2018
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.MaxCut
  ( Problem (..)
  , fromEdges
  , edges
  , buildDSDPMaxCutGraph
  , buildDSDPMaxCutGraph'
  , Solution
  , eval
  , evalEdge
  ) where

import Data.Array.Unboxed
import Data.ByteString.Builder
import Data.ByteString.Builder.Scientific
import qualified Data.ByteString.Lazy.Char8 as BL
import qualified Data.Foldable as F
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Monoid
import Data.Scientific (Scientific)

data Problem a
  = Problem
  { numNodes :: !Int
    -- ^ Number of nodes N. Nodes are numbered from 0 to N-1.
  , numEdges :: !Int
    -- ^ Number of edges.
  , matrix :: IntMap (IntMap a)
    -- ^ Non-zero entries of symmetric weight matrix
  } deriving (Eq, Ord, Show)

instance Functor Problem where
  fmap f Problem{ numNodes = n, numEdges = m, matrix = mat } =
    Problem{ numNodes = n, numEdges = m, matrix = fmap (fmap f) mat }

fromEdges :: Num a => Int -> [(Int,Int,a)] -> Problem a
fromEdges n es = Problem n (length es) $ IntMap.unionsWith (IntMap.unionWith (+)) $
  [IntMap.fromList [(v1, IntMap.singleton v2 w), (v2, IntMap.singleton v1 w)] | (v1,v2,w) <- es]

edges :: Problem a -> [(Int,Int,a)]
edges prob = do
  (a,m) <- IntMap.toList $ matrix prob
  (b,w) <- IntMap.toList $ snd $ IntMap.split a m
  return (a,b,w)

buildDSDPMaxCutGraph :: Problem Scientific -> Builder
buildDSDPMaxCutGraph = buildDSDPMaxCutGraph' scientificBuilder

buildDSDPMaxCutGraph' :: (a -> Builder) -> Problem a -> Builder
buildDSDPMaxCutGraph' weightBuilder prob = header <> body
  where
    header = intDec (numNodes prob) <> char7 ' ' <> intDec (numEdges prob) <> char7 '\n'
    body = mconcat $ do
      (a,b,w) <- edges prob
      return $ intDec (a+1) <> char7 ' ' <> intDec (b+1) <> char7 ' ' <> weightBuilder w <> char7 '\n'

type Solution = UArray Int Bool

eval :: Num a => Solution -> Problem a -> a
eval sol prob = sum [w | (a,b,w) <- edges prob, sol ! a /= sol ! b]

evalEdge :: Num a => Solution -> (Int,Int,a) -> a
evalEdge sol (a,b,w)
  | sol ! a /= sol ! b = w
  | otherwise = 0
