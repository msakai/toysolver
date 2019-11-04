{-# OPTIONS_GHC -Wall #-}
-- {-# LANGUAGE BangPatterns #-}
-- {-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.CNF
-- Copyright   :  (c) Masahiro Sakai 2016-2018
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Reader and Writer for DIMACS CNF and family of similar formats.
--
-----------------------------------------------------------------------------
module ToySolver.Text.CNF {-# DEPRECATED "Use ToySolver.FileFormat.CNF instead" #-}
  (
    CNF (..)

  -- * Parsing .cnf files
  , parseFile
  , parseByteString

  -- * Generating .cnf files
  , writeFile
  , hPutCNF
  , cnfBuilder
  ) where

import Prelude hiding (readFile, writeFile)
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.ByteString.Builder
import System.IO hiding (readFile, writeFile)

import ToySolver.FileFormat.CNF

-- | Parse a CNF file but returns an error message when parsing fails.
{-# DEPRECATED parseByteString "Use FileFormat.parse instead" #-}
parseByteString :: BS.ByteString -> Either String CNF
parseByteString = parse

-- | Encode a 'CNF' to a 'Builder'
{-# DEPRECATED cnfBuilder "Use FileFormat.render instead" #-}
cnfBuilder :: CNF -> Builder
cnfBuilder = render

-- | Output a 'CNF' to a Handle.
{-# DEPRECATED hPutCNF "Use FileFormat.render instead" #-}
hPutCNF :: Handle -> CNF -> IO ()
hPutCNF h cnf = hPutBuilder h (cnfBuilder cnf)
