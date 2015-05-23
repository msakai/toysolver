{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.PseudoBoolean
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

module ToySolver.Data.PseudoBoolean
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
  -- $ParsingOPB
  , parseOPBString
  , parseOPBByteString
  , parseOPBFile

  -- * Parsing WBO files
  -- $ParsingWBO
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

import ToySolver.Data.PseudoBoolean.Parsec
import ToySolver.Data.PseudoBoolean.Types
import ToySolver.Data.PseudoBoolean.Builder
import ToySolver.Data.PseudoBoolean.ByteStringBuilder as ByteStringBuilder

-- $ParsingOPB
-- These functions are based on Parsec.
-- If you want faster parser, you can also use "ToySolver.Data.PseudoBoolean.Attoparsec" module.

-- $ParsingWBO
-- These functions are based on Parsec. 
-- If you want faster parser, you can also use "ToySolver.Data.PseudoBoolean.Attoparsec" module.
