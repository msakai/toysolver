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
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Data.MIP.FileUtils
  ( ParseError
  ) where

#if MIN_VERSION_megaparsec(6,0,0)
import Data.Void
#endif
import qualified Text.Megaparsec as MP

#if MIN_VERSION_megaparsec(7,0,0)
type ParseError s = MP.ParseErrorBundle s Void
#elif MIN_VERSION_megaparsec(6,0,0)
type ParseError s = MP.ParseError (MP.Token s) Void
#else
type ParseError s = MP.ParseError (MP.Token s) MP.Dec
#endif
