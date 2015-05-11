{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.PBFile
-- Copyright   :  (c) Masahiro Sakai 2011-2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Portability :  non-portable (BangPatterns)
--
-- A parser library for .opb file and .wbo files used by PB Competition.
-- 
-- References:
--
-- * Input/Output Format and Solver Requirements for the Competitions of
--   Pseudo-Boolean Solvers
--   <http://www.cril.univ-artois.fr/PB11/format.pdf>
--
-----------------------------------------------------------------------------

module ToySolver.Text.PBFile
  (
  -- * Abstract Syntax
    Formula (..)
  , Constraint
  , Op (..)
  , SoftFormula (..)
  , SoftConstraint
  , Sum
  , WeightedTerm
  , Term
  , Lit
  , Var

  -- * Parsing .opb files
  , parseOPBString
  , parseOPBByteString
  , parseOPBFile

  -- * Parsing .wbo files
  , parseWBOString
  , parseWBOByteString
  , parseWBOFile

  -- * Show .opb files
  , renderOPB
  , renderOPBByteString
  , writeOPBFile
  , hPutOPB

  -- * Show .wbo files
  , renderWBO
  , renderWBOByteString
  , writeWBOFile
  , hPutWBO
  ) where

import Prelude hiding (sum)
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString.Builder as Builder
import qualified Data.DList as DList
import System.IO
import ToySolver.Text.PBFile.Parsec
import ToySolver.Text.PBFile.Attoparsec hiding (parseOPBFile, parseWBOFile)
import ToySolver.Text.PBFile.Types
import ToySolver.Text.PBFile.Builder
import qualified ToySolver.Text.PBFile.ByteStringBuilder as ByteStringBuilder

renderOPB :: Formula -> String
renderOPB opb = DList.apply (opbBuilder opb) ""

renderWBO :: SoftFormula -> String
renderWBO wbo = DList.apply (wboBuilder wbo) ""

renderOPBByteString :: Formula -> BS.ByteString
renderOPBByteString opb = Builder.toLazyByteString (ByteStringBuilder.opbBuilder opb)

renderWBOByteString :: SoftFormula -> BS.ByteString
renderWBOByteString wbo = Builder.toLazyByteString (ByteStringBuilder.wboBuilder wbo)

writeOPBFile :: FilePath -> Formula -> IO ()
writeOPBFile filepath opb = withBinaryFile filepath WriteMode $ \h -> do
  hSetBuffering h (BlockBuffering Nothing)
  hPutOPB h opb

writeWBOFile :: FilePath -> SoftFormula -> IO ()
writeWBOFile filepath wbo = withBinaryFile filepath WriteMode $ \h -> do
  hSetBuffering h (BlockBuffering Nothing)
  hPutWBO h wbo

-- It is recommended that the 'Handle' is set to binary and
-- 'BlockBuffering' mode. See 'hSetBinaryMode' and 'hSetBuffering'.
hPutOPB :: Handle -> Formula -> IO ()
hPutOPB h opb = Builder.hPutBuilder h (opbBuilder opb)

-- It is recommended that the 'Handle' is set to binary and
-- 'BlockBuffering' mode. See 'hSetBinaryMode' and 'hSetBuffering'.
hPutWBO :: Handle -> SoftFormula -> IO ()
hPutWBO h wbo = Builder.hPutBuilder h (wboBuilder wbo)

