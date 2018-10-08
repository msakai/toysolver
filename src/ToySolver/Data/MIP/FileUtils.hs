{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.MIP.FileUtils
-- Copyright   :  (c) Masahiro Sakai 2018
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Data.MIP.FileUtils
  ( ParseError
  ) where

#if MIN_VERSION_megaparsec(6,0,0)
import Data.Void
#endif
import qualified Text.Megaparsec as MP

#if MIN_VERSION_megaparsec(6,0,0)
type ParseError = MP.ParseError Char Void
#elif MIN_VERSION_megaparsec(5,0,0)
type ParseError = MP.ParseError Char MP.Dec
#else
type ParseError = MP.ParseError
#endif
