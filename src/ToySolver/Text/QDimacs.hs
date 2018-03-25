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
-- References:
--
-- * QDIMACS standard Ver. 1.1
--   <http://www.qbflib.org/qdimacs.html>
--
-----------------------------------------------------------------------------
module ToySolver.Text.QDimacs
  (
  -- * FileFormat class
    FileFormat (..)
  , parseFile
  , writeFile

  -- * QDIMACS format
  , QDimacs (..)
  , Quantifier (..)
  , QuantSet
  , Atom
  , Lit
  , Clause
  , PackedClause
  , packClause
  , unpackClause
  , hPutQDimacs
  , qdimacsBuilder
  ) where

import Prelude hiding (writeFile)
import ToySolver.SAT.Types (Clause, Lit, PackedClause, packClause, unpackClause)
import ToySolver.Text.CNF
