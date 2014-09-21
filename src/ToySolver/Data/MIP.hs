{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.MIP
-- Copyright   :  (c) Masahiro Sakai 2011-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Mixed-Integer Programming Problems with some commmonly used extensions
--
-----------------------------------------------------------------------------
module ToySolver.Data.MIP
  ( module ToySolver.Data.MIP.Base
  , readFile
  , readLPFile
  , readMPSFile
  , writeFile
  , writeLPFile
  , writeMPSFile
  ) where

import Prelude hiding (readFile, writeFile)
import qualified Prelude as P
import Data.Char
import System.FilePath (takeExtension)
import Text.Parsec

import ToySolver.Data.MIP.Base
import qualified ToySolver.Text.LPFile as LPFile
import qualified ToySolver.Text.MPSFile as MPSFile

-- | Parse .lp or .mps file based on file extension
readFile :: FilePath -> IO (Either ParseError Problem)
readFile fname =
  case map toLower (takeExtension fname) of
    ".lp"  -> readLPFile fname
    ".mps" -> readMPSFile fname
    ext -> ioError $ userError $ "unknown extension: " ++ ext

-- | Parse a file containing LP file data.
readLPFile :: FilePath -> IO (Either ParseError Problem)
readLPFile = LPFile.parseFile

-- | Parse a file containing MPS file data.
readMPSFile :: FilePath -> IO (Either ParseError Problem)
readMPSFile = MPSFile.parseFile

writeFile :: FilePath -> Problem -> IO ()
writeFile fname prob =
  case map toLower (takeExtension fname) of
    ".lp"  -> writeLPFile fname prob
    ".mps" -> writeMPSFile fname prob
    ext -> ioError $ userError $ "unknown extension: " ++ ext

writeLPFile :: FilePath -> Problem -> IO ()
writeLPFile fname prob =
  case LPFile.render prob of
    Left err -> ioError $ userError err
    Right s -> P.writeFile fname s

writeMPSFile :: FilePath -> Problem -> IO ()
writeMPSFile fname prob = 
  case MPSFile.render prob of
    Left err -> ioError $ userError err
    Right s -> P.writeFile fname s
