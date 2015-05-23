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

import Data.Array.IArray
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS

import qualified ToySolver.Data.PseudoBoolean as PBFile

convert :: DIMACS.CNF -> PBFile.Formula
convert cnf
  = PBFile.Formula
  { PBFile.pbObjectiveFunction = Nothing
  , PBFile.pbConstraints = map f (DIMACS.clauses cnf)
  , PBFile.pbNumVars = DIMACS.numVars cnf
  , PBFile.pbNumConstraints = DIMACS.numClauses cnf
  }
  where
    f clause = ([(1,[l]) | l <- elems clause], PBFile.Ge, 1)
