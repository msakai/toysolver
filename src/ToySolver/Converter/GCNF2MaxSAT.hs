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

import qualified Data.Vector.Generic as VG
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.Text.CNF as CNF

convert :: CNF.GCNF -> CNF.WCNF
convert
  CNF.GCNF
  { CNF.gcnfNumVars        = nv
  , CNF.gcnfNumClauses     = nc
  , CNF.gcnfLastGroupIndex = lastg
  , CNF.gcnfClauses        = cs
  }
  =
  CNF.WCNF
  { CNF.wcnfTopCost = top
  , CNF.wcnfClauses = [(top, if g==0 then c else VG.cons (-(nv+g)) c) | (g,c) <- cs] ++ [(1, SAT.packClause [v]) | v <- [nv+1..nv+lastg]]
  , CNF.wcnfNumVars = nv + lastg
  , CNF.wcnfNumClauses = nc + lastg
  }
  where
    top :: CNF.Weight
    top = fromIntegral (lastg + 1)
