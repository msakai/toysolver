{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.SAT2IP
-- Copyright   :  (c) Masahiro Sakai 2011-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.SAT2IP
  ( convert
  ) where

import Data.Map (Map)
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS

import qualified ToySolver.Data.MIP as MIP
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.Converter.PB2IP as PB2IP
import qualified ToySolver.Converter.SAT2PB as SAT2PB

convert :: DIMACS.CNF -> (MIP.Problem, SAT.Model -> Map MIP.Var Rational, Map MIP.Var Rational -> SAT.Model)
convert cnf = PB2IP.convert (SAT2PB.convert cnf)
