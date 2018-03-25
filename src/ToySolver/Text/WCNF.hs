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
module ToySolver.Text.WCNF
  (
  -- * FileFormat class
    FileFormat (..)
  , parseFile
  , writeFile

  -- * WCNF format
  , WCNF (..)
  , WeightedClause
  , Weight
  , hPutWCNF
  , wcnfBuilder
  ) where

import Prelude hiding (writeFile)
import ToySolver.Text.CNF
