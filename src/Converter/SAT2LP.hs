{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Converter.SAT2LP
-- Copyright   :  (c) Masahiro Sakai 2011-2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Converter.SAT2LP
  ( ObjType (..)
  , convert 
  ) where

import qualified Data.Map as Map
import qualified Text.LPFile as LPFile
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS
import qualified SAT.Types as SAT
import qualified Converter.PB2LP as PB2LP
import qualified Converter.SAT2PB as SAT2PB
import Converter.ObjType

convert :: ObjType -> DIMACS.CNF -> (LPFile.LP, Map.Map LPFile.Var Rational -> SAT.Model)
convert objType cnf = PB2LP.convert objType (SAT2PB.convert cnf)
