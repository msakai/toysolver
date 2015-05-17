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
-- A library for parsing\/generating OPB\/WBO files used in pseudo boolean competition.
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

  -- * Parsing OPB files
  , parseOPBString
  , parseOPBByteString
  , parseOPBFile

  -- * Parsing WBO files
  , parseWBOString
  , parseWBOByteString
  , parseWBOFile

  -- * Generating OPB files
  , toOPBString
  , toOPBByteString
  , writeOPBFile
  , hPutOPB

  -- * Generating WBO files
  , toWBOString
  , toWBOByteString
  , writeWBOFile
  , hPutWBO
  ) where

import ToySolver.Text.PBFile.Parsec
import ToySolver.Text.PBFile.Types
import ToySolver.Text.PBFile.Builder
import ToySolver.Text.PBFile.ByteStringBuilder as ByteStringBuilder
