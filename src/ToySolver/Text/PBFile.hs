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
import ToySolver.Text.PBFile.Parsec
import ToySolver.Text.PBFile.Attoparsec hiding (parseOPBFile, parseWBOFile)
import ToySolver.Text.PBFile.Types
import ToySolver.Text.PBFile.Builder
import ToySolver.Text.PBFile.ByteStringBuilder as ByteStringBuilder
