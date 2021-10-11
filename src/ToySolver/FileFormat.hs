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
  , WithFastParser (..)
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
  parse s =
    case PBFileMegaparsec.parseOPBByteString "-" s of
      Left err -> Left (errorBundlePretty err)
      Right x -> Right x
  render x = PBFileBB.opbBuilder x

instance FileFormat PBFile.SoftFormula where
  parse s =
    case PBFileMegaparsec.parseWBOByteString "-" s of
      Left err -> Left (errorBundlePretty err)
      Right x -> Right x
  render x = PBFileBB.wboBuilder x

-- | Wrapper type for parsing opb/wbo files using attoparsec-based parser instead of megaparsec-based one.
newtype WithFastParser a
  = WithFastParser
  { unWithFastParser :: a
  }

instance FileFormat (WithFastParser PBFile.Formula) where
  parse = fmap WithFastParser . PBFileAttoparsec.parseOPBByteString
  render (WithFastParser x) = PBFileBB.opbBuilder x

instance FileFormat (WithFastParser PBFile.SoftFormula) where
  parse = fmap WithFastParser . PBFileAttoparsec.parseWBOByteString
  render (WithFastParser x) = PBFileBB.wboBuilder x
