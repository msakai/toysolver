{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.FileFormat
-- Copyright   :  (c) Masahiro Sakai 2018
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.FileFormat
  ( module ToySolver.FileFormat.Base
  ) where

import qualified Data.PseudoBoolean as PBFile
import qualified Data.PseudoBoolean.Attoparsec as PBFileAttoparsec
import qualified Data.PseudoBoolean.ByteStringBuilder as PBFileBB
import ToySolver.FileFormat.Base
import ToySolver.Text.CNF () -- importing instances

instance FileFormat PBFile.Formula where
  parse = PBFileAttoparsec.parseOPBByteString
  render = PBFileBB.opbBuilder

instance FileFormat PBFile.SoftFormula where
  parse = PBFileAttoparsec.parseWBOByteString
  render = PBFileBB.wboBuilder
