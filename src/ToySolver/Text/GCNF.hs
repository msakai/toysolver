{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.GCNF
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Text.GCNF {-# DEPRECATED "Use ToySolver.FileFormat.CNF instead" #-}
  (
    GCNF (..)
  , GroupIndex
  , GClause

  -- * Parsing .gcnf files
  , parseByteString
  , parseFile

  -- * Generating .gcnf files
  , writeFile
  , hPutGCNF
  , gcnfBuilder
  ) where

import Prelude hiding (writeFile)
import Data.ByteString.Builder
import qualified Data.ByteString.Lazy.Char8 as BL
import System.IO hiding (writeFile)
import ToySolver.FileFormat.CNF hiding (parseByteString)

-- | Parse a GCNF file but returns an error message when parsing fails.
{-# DEPRECATED parseByteString "Use FileFormat.parse instead" #-}
parseByteString :: BL.ByteString -> Either String GCNF
parseByteString = parse

-- | Encode a 'GCNF' to a 'Builder'
{-# DEPRECATED gcnfBuilder "Use FileFormat.render instead" #-}
gcnfBuilder :: GCNF -> Builder
gcnfBuilder = render

-- | Output a 'GCNF' to a Handle.
{-# DEPRECATED hPutGCNF "Use FileFormat.render instead" #-}
hPutGCNF :: Handle -> GCNF -> IO ()
hPutGCNF h gcnf = hPutBuilder h (gcnfBuilder gcnf)
