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
  , parseLPString
  , parseMPSString
  , writeFile
  , writeLPFile
  , writeMPSFile
  , toLPString
  , toMPSString
  ) where

import Prelude hiding (readFile, writeFile)
import Data.Char
import System.FilePath (takeExtension)
import System.IO hiding (readFile, writeFile)
import Text.Parsec

import ToySolver.Data.MIP.Base
import qualified ToySolver.Data.MIP.LPFile as LPFile
import qualified ToySolver.Data.MIP.MPSFile as MPSFile

-- | Parse .lp or .mps file based on file extension
readFile :: (IsVar v, RealFrac c) => FileOptions -> FilePath -> IO (Either ParseError (Problem v c))
readFile opt fname =
  case map toLower (takeExtension fname) of
    ".lp"  -> readLPFile opt fname
    ".mps" -> readMPSFile opt fname
    ext -> ioError $ userError $ "unknown extension: " ++ ext

-- | Parse a file containing LP file data.
readLPFile :: (IsVar v, RealFrac c) => FileOptions -> FilePath -> IO (Either ParseError (Problem v c))
readLPFile = LPFile.parseFile

-- | Parse a file containing MPS file data.
readMPSFile :: (IsVar v, RealFrac c) => FileOptions -> FilePath -> IO (Either ParseError (Problem v c))
readMPSFile = MPSFile.parseFile

-- | Parse a string containing LP file data.
parseLPString :: (IsVar v, RealFrac c) => FileOptions -> SourceName -> String -> Either ParseError (Problem v c)
parseLPString = LPFile.parseString

-- | Parse a string containing MPS file data.
parseMPSString :: (IsVar v, RealFrac c) => FileOptions -> SourceName -> String -> Either ParseError (Problem v c)
parseMPSString = MPSFile.parseString

writeFile :: (IsVar v, RealFrac c) => FileOptions -> FilePath -> Problem v c -> IO ()
writeFile opt fname prob =
  case map toLower (takeExtension fname) of
    ".lp"  -> writeLPFile opt fname prob
    ".mps" -> writeMPSFile opt fname prob
    ext -> ioError $ userError $ "unknown extension: " ++ ext

writeLPFile :: (IsVar v, RealFrac c) => FileOptions -> FilePath -> Problem v c -> IO ()
writeLPFile opt fname prob =
  case LPFile.render opt prob of
    Left err -> ioError $ userError err
    Right s ->
      withFile fname WriteMode $ \h -> do
        case optFileEncoding opt of
          Nothing -> return ()
          Just enc -> hSetEncoding h enc
        hPutStr h s

writeMPSFile :: (IsVar v, RealFrac c) => FileOptions -> FilePath -> Problem v c -> IO ()
writeMPSFile opt fname prob = 
  case MPSFile.render opt prob of
    Left err -> ioError $ userError err
    Right s ->
      withFile fname WriteMode $ \h -> do
        case optFileEncoding opt of
          Nothing -> return ()
          Just enc -> hSetEncoding h enc
        hPutStr h s

toLPString :: (IsVar v, RealFrac c) => FileOptions -> Problem v c -> Either String String
toLPString = LPFile.render

toMPSString :: (IsVar v, RealFrac c) => FileOptions -> Problem v c -> Either String String
toMPSString = MPSFile.render
