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
-- References:
-- 
-- * <http://www.satcompetition.org/2011/rules.pdf>
--
--
-----------------------------------------------------------------------------
module ToySolver.Text.GCNF {-# DEPRECATED "Use ToySolver.Text.CNF instead" #-}
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
import System.IO hiding (writeFile)
import ToySolver.Text.CNF

{-# DEPRECATED gcnfBuilder "Use FileFormat.render instead" #-}
gcnfBuilder :: GCNF -> Builder
gcnfBuilder = render

{-# DEPRECATED hPutGCNF "Use FileFormat.render instead" #-}
hPutGCNF :: Handle -> GCNF -> IO ()
hPutGCNF h gcnf = hPutBuilder h (gcnfBuilder gcnf)
