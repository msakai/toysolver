{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.MaxSAT2IP
-- Copyright   :  (c) Masahiro Sakai 2011-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.MaxSAT2IP
  ( convert
  ) where

import Data.Map (Map)
import qualified ToySolver.Data.MIP as MIP
import qualified ToySolver.Text.CNF as CNF
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.Converter.MaxSAT2WBO as MaxSAT2WBO
import qualified ToySolver.Converter.PB2IP as PB2IP

convert :: Bool -> CNF.WCNF -> (MIP.Problem Integer, SAT.Model -> Map MIP.Var Rational, Map MIP.Var Rational -> SAT.Model)
convert useIndicator wcnf = PB2IP.convertWBO useIndicator (MaxSAT2WBO.convert wcnf)
