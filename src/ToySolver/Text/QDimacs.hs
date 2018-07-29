{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.QDimacs
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Text.QDimacs {-# DEPRECATED "Use ToySolver.FileFormat.CNF instead" #-}
  ( QDimacs (..)
  , Quantifier (..)
  , QuantSet
  , Atom
  , Lit
  , Clause
  , PackedClause
  , packClause
  , unpackClause
  , parseFile
  , parseByteString

  -- * Generating .qdimacs files
  , writeFile
  , hPutQDimacs
  , qdimacsBuilder
  ) where

import Prelude hiding (writeFile)
import Data.ByteString.Builder
import qualified Data.ByteString.Lazy.Char8 as BL
import System.IO hiding (writeFile)
import ToySolver.SAT.Types (Clause, Lit, PackedClause, packClause, unpackClause)
import ToySolver.FileFormat.CNF hiding (parseByteString)

-- | Parse a QDimacs file but returns an error message when parsing fails.
{-# DEPRECATED parseByteString "Use FileFormat.parse instead" #-}
parseByteString :: BL.ByteString -> Either String QDimacs
parseByteString = parse

-- | Encode a 'QDimacs' to a 'Builder'
{-# DEPRECATED qdimacsBuilder "Use FileFormat.render instead" #-}
qdimacsBuilder :: QDimacs -> Builder
qdimacsBuilder = render

-- | Output a 'QDimacs' to a Handle.
{-# DEPRECATED hPutQDimacs "Use FileFormat.render instead" #-}
hPutQDimacs :: Handle -> QDimacs -> IO ()
hPutQDimacs h qdimacs = hPutBuilder h (qdimacsBuilder qdimacs)
