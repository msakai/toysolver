{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.SAT2MaxCut
-- Copyright   :  (c) Masahiro Sakai 2018
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- http://www.cs.cornell.edu/courses/cs4820/2014sp/notes/reduction-maxcut.pdf
--
-----------------------------------------------------------------------------
module ToySolver.Converter.SAT2MaxCut
  (
  -- * SAT to MaxCut conversion
    SAT2MaxCutInfo
  , sat2maxcut
  , sat2maxcut_forward
  , sat2maxcut_backward

  -- * Low-level conversion

  -- ** NAE-SAT to MaxCut
  , NAESAT2MaxCutInfo
  , naesat2maxcut
  , naesat2maxcut_forward
  , naesat2maxcut_backward

  -- ** NAE-3-SAT to MaxCut
  , NAE3SAT2MaxCutInfo
  , nae3sat2maxcut
  , nae3sat2maxcut_forward
  , nae3sat2maxcut_backward
  ) where

import Data.Array.Unboxed
import qualified Data.IntSet as IntSet
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU

import qualified ToySolver.MaxCut as MaxCut
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.Text.CNF as CNF
import ToySolver.Converter.NAESAT (NAESAT)
import qualified ToySolver.Converter.NAESAT as NAESAT

-- ------------------------------------------------------------------------

type SAT2MaxCutInfo = (NAESAT.SAT2NAESATInfo, NAESAT2MaxCutInfo)

sat2maxcut :: CNF.CNF -> (MaxCut.Problem Integer, SAT2MaxCutInfo)
sat2maxcut x = (x2, (info1, info2))
  where
    (x1, info1) = NAESAT.sat2naesat x
    (x2, info2) = naesat2maxcut x1

sat2maxcut_forward :: SAT2MaxCutInfo -> SAT.Model -> UArray Int Bool
sat2maxcut_forward (info1,info2) =
  naesat2maxcut_forward info2 . NAESAT.sat2naesat_forward info1

sat2maxcut_backward :: SAT2MaxCutInfo -> UArray Int Bool -> SAT.Model
sat2maxcut_backward (info1,info2) =
  NAESAT.sat2naesat_backward info1 . naesat2maxcut_backward info2

-- ------------------------------------------------------------------------

type NAESAT2MaxCutInfo = (NAESAT.NAESAT2NAEKSATInfo, NAE3SAT2MaxCutInfo)

naesat2maxcut :: NAESAT -> (MaxCut.Problem Integer, NAESAT2MaxCutInfo)
naesat2maxcut x = (x2, (info1, info2))
  where
    (x1, info1) = NAESAT.naesat2naeksat 3 x
    (x2, info2) = nae3sat2maxcut x1

naesat2maxcut_forward :: NAESAT2MaxCutInfo -> SAT.Model -> UArray Int Bool
naesat2maxcut_forward (info1,info2) =
  nae3sat2maxcut_forward info2 . NAESAT.naesat2naeksat_forward info1

naesat2maxcut_backward :: NAESAT2MaxCutInfo -> UArray Int Bool -> SAT.Model
naesat2maxcut_backward (info1,info2) =
  NAESAT.naesat2naeksat_backward info1 . nae3sat2maxcut_backward info2

-- ------------------------------------------------------------------------

type NAE3SAT2MaxCutInfo = Integer

-- Original nae-sat problem is satisfiable iff Max-Cut problem has solution with >=threshold.
nae3sat2maxcut :: NAESAT -> (MaxCut.Problem Integer, NAE3SAT2MaxCutInfo)
nae3sat2maxcut (n,cs)
  | any (\c -> VG.length c < 2) cs' =
      ( MaxCut.fromEdges (n*2) []
      , 1
      )
  | otherwise =
      ( MaxCut.fromEdges (n*2) (variableEdges ++ clauseEdges)
      , bigM * fromIntegral n + clauseEdgesObjMax
      )
  where
    cs' = map (VG.fromList . IntSet.toList . IntSet.fromList . VG.toList) cs

    bigM = clauseEdgesObjMax + 1

    (clauseEdges, clauseEdgesObjMax) = foldl f ([],0) cs'
      where
        f :: ([(Int,Int,Integer)], Integer) -> VU.Vector SAT.Lit -> ([(Int,Int,Integer)], Integer)
        f (clauseEdges', !clauseEdgesObjMax') c =
          case map encodeLit (VG.toList c) of
            []  -> error "nae3sat2maxcut: should not happen"
            [_] -> error "nae3sat2maxcut: should not happen"
            [v0,v1]    -> ([(v0, v1, 1)] ++ clauseEdges', clauseEdgesObjMax' + 1)
            [v0,v1,v2] -> ([(v0, v1, 1), (v1, v2, 1), (v2, v0, 1)] ++ clauseEdges', clauseEdgesObjMax' + 2)
            _ -> error "nae3sat2maxcut: cannot handle nae-clause of size >3"

    variableEdges = [(encodeLit v, encodeLit (-v), bigM) | v <- [1..n]]

nae3sat2maxcut_forward :: NAE3SAT2MaxCutInfo -> SAT.Model -> MaxCut.Solution
nae3sat2maxcut_forward _ m = array (0,2*n-1) $ do
  v <- [1..n]
  let val = SAT.evalVar m v
  [(encodeLit v, val), (encodeLit (-v), not val)]
  where
    (_,n) = bounds m

nae3sat2maxcut_backward :: NAE3SAT2MaxCutInfo -> MaxCut.Solution -> SAT.Model
nae3sat2maxcut_backward _ sol = array (1,n) [(v, sol ! encodeLit v) | v <- [1..n]]
  where
    (_,n') = bounds sol
    n = (n'+1) `div` 2

-- ------------------------------------------------------------------------

encodeLit :: SAT.Lit -> Int
encodeLit l =
  if l > 0
  then (l-1)*2
  else (-l-1)*2+1

-- ------------------------------------------------------------------------
