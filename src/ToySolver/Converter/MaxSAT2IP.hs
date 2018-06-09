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
  ( maxsat2ip
  , MaxSAT2IPInfo
  ) where

import qualified ToySolver.Data.MIP as MIP
import qualified ToySolver.Text.CNF as CNF
import ToySolver.Converter.Base
import ToySolver.Converter.PB
import ToySolver.Converter.PB2IP

type MaxSAT2IPInfo = ComposedTransformer MaxSAT2WBOInfo WBO2IPInfo

maxsat2ip :: Bool -> CNF.WCNF -> (MIP.Problem Integer, MaxSAT2IPInfo)
maxsat2ip useIndicator wcnf = (ip, ComposedTransformer info1 info2)
  where
    (wbo, info1) = maxsat2wbo wcnf
    (ip, info2) = wbo2ip useIndicator wbo
