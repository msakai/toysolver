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
  , SAT2PBInfo
  ) where

import qualified Data.PseudoBoolean as PBFile
import ToySolver.Converter.Base
import ToySolver.SAT.Types as SAT
import qualified ToySolver.Text.CNF as CNF

type SAT2PBInfo = IdentityTransformer SAT.Model

convert :: CNF.CNF -> (PBFile.Formula, SAT2PBInfo)
convert cnf
  = ( PBFile.Formula
      { PBFile.pbObjectiveFunction = Nothing
      , PBFile.pbConstraints = map f (CNF.cnfClauses cnf)
      , PBFile.pbNumVars = CNF.cnfNumVars cnf
      , PBFile.pbNumConstraints = CNF.cnfNumClauses cnf
      }
    , IdentityTransformer
    )
  where
    f clause = ([(1,[l]) | l <- SAT.unpackClause clause], PBFile.Ge, 1)
