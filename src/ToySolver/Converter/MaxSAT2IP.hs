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
  , MaxSAT2IPInfo
  ) where

import qualified ToySolver.Data.MIP as MIP
import qualified ToySolver.Text.CNF as CNF
import ToySolver.Converter.Base
import ToySolver.Converter.PB
import qualified ToySolver.Converter.PB2IP as PB2IP

type MaxSAT2IPInfo = ComposedTransformer MaxSAT2WBOInfo PB2IP.WBO2IPInfo

convert :: Bool -> CNF.WCNF -> (MIP.Problem Integer, MaxSAT2IPInfo)
convert useIndicator wcnf = (ip, ComposedTransformer info1 info2)
  where
    (wbo, info1) = maxsat2wbo wcnf
    (ip, info2) = PB2IP.convertWBO useIndicator wbo
