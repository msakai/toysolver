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
module ToySolver.Text.GCNF
  (
  -- * FileFormat class
    FileFormat (..)
  , parseFile
  , writeFile

  -- * GCNF format
  , GCNF (..)
  , GroupIndex
  , GClause
  , hPutGCNF
  , gcnfBuilder
  ) where

import Prelude hiding (writeFile)
import ToySolver.Text.CNF
