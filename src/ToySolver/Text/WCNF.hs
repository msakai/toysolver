{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.WCNF
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Text.WCNF {-# DEPRECATED "Use ToySolver.FileFormat.CNF instead" #-}
  (
    WCNF (..)
  , WeightedClause
  , Weight

  -- * Parsing .cnf/.wcnf files
  , parseFile
  , parseByteString

  -- * Generating .wcnf files
  , writeFile
  , hPutWCNF
  , wcnfBuilder
  ) where

import Prelude hiding (writeFile)
import Data.ByteString.Builder
import qualified Data.ByteString.Lazy.Char8 as BL
import System.IO hiding (writeFile)
import ToySolver.FileFormat.CNF

-- | Parse a WCNF file but returns an error message when parsing fails.
{-# DEPRECATED parseByteString "Use FileFormat.parse instead" #-}
parseByteString :: BL.ByteString -> Either String WCNF
parseByteString = parse

-- | Encode a 'WCNF' to a 'Builder'
{-# DEPRECATED wcnfBuilder "Use FileFormat.render instead" #-}
wcnfBuilder :: WCNF -> Builder
wcnfBuilder = render

-- | Output a 'WCNF' to a Handle.
{-# DEPRECATED hPutWCNF "Use FileFormat.render instead" #-}
hPutWCNF :: Handle -> WCNF -> IO ()
hPutWCNF h wcnf = hPutBuilder h (wcnfBuilder wcnf)
