{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Converter.SAT2LP
-- Copyright   :  (c) Masahiro Sakai 2011-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Converter.SAT2LP
  ( convert
  ) where

import Data.Map (Map)
import qualified Data.MIP as MIP
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS
import qualified SAT.Types as SAT
import qualified Converter.PB2LP as PB2LP
import qualified Converter.SAT2PB as SAT2PB

convert :: DIMACS.CNF -> (MIP.Problem, Map MIP.Var Rational -> SAT.Model)
convert cnf = PB2LP.convert (SAT2PB.convert cnf)
