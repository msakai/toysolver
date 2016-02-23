{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.GCNF2MaxSAT
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.GCNF2MaxSAT
  ( convert
  ) where

import qualified ToySolver.Text.GCNF as GCNF
import qualified ToySolver.Text.MaxSAT as MaxSAT

convert :: GCNF.GCNF -> MaxSAT.WCNF
convert
  GCNF.GCNF
  { GCNF.numVars        = nv
  , GCNF.numClauses     = nc
  , GCNF.lastGroupIndex = lastg
  , GCNF.clauses        = cs
  }
  =
  MaxSAT.WCNF
  { MaxSAT.topCost = top
  , MaxSAT.clauses = [(top, if g==0 then c else -(nv+g) : c) | (g,c) <- cs] ++ [(1,[v]) | v <- [nv+1..nv+lastg]]
  , MaxSAT.numVars = nv + lastg
  , MaxSAT.numClauses = nc + lastg
  }
  where
    top :: MaxSAT.Weight
    top = fromIntegral (lastg + 1)
