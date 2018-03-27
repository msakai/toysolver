{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.MaxSAT2WBO
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.MaxSAT2WBO
  ( convert
  ) where

import qualified Data.PseudoBoolean as PBFile
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.Text.CNF as CNF

convert :: CNF.WCNF -> PBFile.SoftFormula
convert
  CNF.WCNF
  { CNF.wcnfTopCost = top
  , CNF.wcnfClauses = cs
  , CNF.wcnfNumVars = nv
  , CNF.wcnfNumClauses = nc
  } =
  PBFile.SoftFormula
  { PBFile.wboTopCost = Nothing
  , PBFile.wboConstraints = map f cs
  , PBFile.wboNumVars = nv
  , PBFile.wboNumConstraints = nc
  }
  where
    f (w,c)
     | w>=top    = (Nothing, p) -- hard constraint
     | otherwise = (Just w, p)  -- soft constraint
     where
       p = ([(1,[l]) | l <- SAT.unpackClause c], PBFile.Ge, 1)

