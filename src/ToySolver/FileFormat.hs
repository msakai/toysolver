{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
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
  , WithMegaparsecParser (..)
  ) where

import qualified Data.PseudoBoolean as PBFile
import qualified Data.PseudoBoolean.Attoparsec as PBFileAttoparsec
import qualified Data.PseudoBoolean.Megaparsec as PBFileMegaparsec
import qualified Data.PseudoBoolean.ByteStringBuilder as PBFileBB
import ToySolver.FileFormat.Base
import ToySolver.FileFormat.CNF () -- importing instances
import ToySolver.QUBO () -- importing instances
import Text.Megaparsec.Error (errorBundlePretty)

instance FileFormat PBFile.Formula where
  parse = PBFileAttoparsec.parseOPBByteString
  render = PBFileBB.opbBuilder

instance FileFormat PBFile.SoftFormula where
  parse = PBFileAttoparsec.parseWBOByteString
  render = PBFileBB.wboBuilder


-- | Wrapper type for parsing opb/wbo files using megaparsec-based parser instead of attoparsec-based one.
newtype WithMegaparsecParser a
  = WithMegaparsecParser
  { unWithMegaparsecParser :: a
  }

instance FileFormat (WithMegaparsecParser PBFile.Formula) where
  parse s =
    case PBFileMegaparsec.parseOPBByteString "-" s of
      Left err -> Left (errorBundlePretty err)
      Right x -> Right (WithMegaparsecParser x)
  render (WithMegaparsecParser x) = PBFileBB.opbBuilder x

instance FileFormat (WithMegaparsecParser PBFile.SoftFormula) where
  parse s =
    case PBFileMegaparsec.parseWBOByteString "-" s of
      Left err -> Left (errorBundlePretty err)
      Right x -> Right (WithMegaparsecParser x)
  render (WithMegaparsecParser x) = PBFileBB.wboBuilder x

