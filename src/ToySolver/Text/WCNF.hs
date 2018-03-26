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
-- References:
-- 
-- * <http://maxsat.ia.udl.cat/requirements/>
--
-----------------------------------------------------------------------------
module ToySolver.Text.WCNF {-# DEPRECATED "Use ToySolver.Text.CNF instead" #-}
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
import ToySolver.Text.CNF hiding (parseByteString)

{-# DEPRECATED parseByteString "Use FileFormat.parse instead" #-}
parseByteString :: BL.ByteString -> Either String WCNF
parseByteString = parse

{-# DEPRECATED wcnfBuilder "Use FileFormat.render instead" #-}
wcnfBuilder :: WCNF -> Builder
wcnfBuilder = render

{-# DEPRECATED hPutWCNF "Use FileFormat.render instead" #-}
hPutWCNF :: Handle -> WCNF -> IO ()
hPutWCNF h wcnf = hPutBuilder h (wcnfBuilder wcnf)
