{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Converter.MaxSAT2LP
-- Copyright   :  (c) Masahiro Sakai 2011-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Converter.MaxSAT2LP
  ( convert
  ) where

import Data.Map (Map)
import qualified Data.MIP as MIP
import qualified Text.MaxSAT as MaxSAT
import SAT.Types
import qualified Converter.MaxSAT2WBO as MaxSAT2WBO
import qualified Converter.PB2LP as PB2LP

convert :: Bool -> MaxSAT.WCNF -> (MIP.Problem, Map MIP.Var Rational -> Model)
convert useIndicator wcnf = PB2LP.convertWBO useIndicator (MaxSAT2WBO.convert wcnf)
