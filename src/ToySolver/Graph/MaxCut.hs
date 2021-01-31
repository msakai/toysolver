-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Graph.MaxCut
-- Copyright   :  (c) Masahiro Sakai 2018
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Graph.MaxCut
  ( Problem (..)
  , buildDSDPMaxCutGraph
  , buildDSDPMaxCutGraph'
  , Solution
  , eval
  , evalEdge
  ) where

import Data.Array.IArray
import Data.Array.Unboxed
import Data.ByteString.Builder
import Data.ByteString.Builder.Scientific
import qualified Data.ByteString.Lazy.Char8 as BL
import qualified Data.Foldable as F
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Monoid
import Data.Scientific (Scientific)

import ToySolver.Graph.Base

type Problem a = EdgeLabeledGraph a

buildDSDPMaxCutGraph :: EdgeLabeledGraph Scientific -> Builder
buildDSDPMaxCutGraph = buildDSDPMaxCutGraph' scientificBuilder

buildDSDPMaxCutGraph' :: (a -> Builder) -> EdgeLabeledGraph a -> Builder
buildDSDPMaxCutGraph' weightBuilder prob = header <> body
  where
    (lb,ub) = bounds prob
    m = sum [IntMap.size m | m <- elems prob]
    header = intDec (ub-lb+1) <> char7 ' ' <> intDec m <> char7 '\n'
    body = mconcat $ do
      (a,b,w) <- graphToUnorderedEdges prob
      return $ intDec (a-lb+1) <> char7 ' ' <> intDec (b-lb+1) <> char7 ' ' <> weightBuilder w <> char7 '\n'

type Solution = UArray Int Bool

eval :: Num a => Solution -> Problem a -> a
eval sol prob = sum [w | (a,b,w) <- graphToUnorderedEdges prob, sol ! a /= sol ! b]

evalEdge :: Num a => Solution -> (Int,Int,a) -> a
evalEdge sol (a,b,w)
  | sol ! a /= sol ! b = w
  | otherwise = 0
