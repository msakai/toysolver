{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Converter.SAT2PB
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Converter.SAT2PB
  ( convert
  ) where

import Data.Array.IArray
import qualified Text.PBFile as PBFile
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS

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
