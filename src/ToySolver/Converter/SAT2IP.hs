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
  , SAT2IPInfo
  ) where

import qualified ToySolver.Data.MIP as MIP
import ToySolver.Converter.Base
import qualified ToySolver.Converter.PB2IP as PB2IP
import ToySolver.Converter.PB
import qualified ToySolver.Text.CNF as CNF

type SAT2IPInfo = ComposedTransformer SAT2PBInfo PB2IP.PB2IPInfo

convert :: CNF.CNF -> (MIP.Problem Integer, SAT2IPInfo)
convert cnf = (ip, ComposedTransformer info1 info2)
  where
    (pb,info1) = sat2pb cnf
    (ip,info2) = PB2IP.convert pb
