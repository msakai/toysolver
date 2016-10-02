{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.SAT2PB
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.SAT2PB
  ( convert
  ) where

import qualified Data.PseudoBoolean as PBFile
import qualified ToySolver.Text.CNF as CNF

convert :: CNF.CNF -> PBFile.Formula
convert cnf
  = PBFile.Formula
  { PBFile.pbObjectiveFunction = Nothing
  , PBFile.pbConstraints = map f (CNF.clauses cnf)
  , PBFile.pbNumVars = CNF.numVars cnf
  , PBFile.pbNumConstraints = CNF.numClauses cnf
  }
  where
    f clause = ([(1,[l]) | l <- clause], PBFile.Ge, 1)
