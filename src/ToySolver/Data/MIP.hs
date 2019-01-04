{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.MIP
-- Copyright   :  (c) Masahiro Sakai 2011-2014
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
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
  , ParseError
  ) where

import Prelude hiding (readFile, writeFile)
import Control.Exception
import Data.Char
import Data.Scientific (Scientific)
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TLIO
import System.FilePath (takeExtension, splitExtension)
import System.IO hiding (readFile, writeFile)

import ToySolver.Data.MIP.Base
import ToySolver.Data.MIP.FileUtils (ParseError)
import qualified ToySolver.Data.MIP.LPFile as LPFile
import qualified ToySolver.Data.MIP.MPSFile as MPSFile

#ifdef WITH_ZLIB
import qualified Codec.Compression.GZip as GZip
import qualified Data.ByteString.Lazy as BL
import Data.ByteString.Lazy.Encoding (encode, decode)
import qualified Data.CaseInsensitive as CI
import GHC.IO.Encoding (getLocaleEncoding)
#endif

-- | Parse .lp or .mps file based on file extension
readFile :: FileOptions -> FilePath -> IO (Problem Scientific)
readFile opt fname =
  case getExt fname of
    ".lp"  -> readLPFile opt fname
    ".mps" -> readMPSFile opt fname
    ext -> ioError $ userError $ "unknown extension: " ++ ext

-- | Parse a file containing LP file data.
readLPFile :: FileOptions -> FilePath -> IO (Problem Scientific)
#ifndef WITH_ZLIB
readLPFile = LPFile.parseFile
#else
readLPFile opt fname = do
  s <- readTextFile opt fname
  let ret = LPFile.parseString opt fname s
  case ret of
    Left e -> throw e
    Right a -> return a
#endif

-- | Parse a file containing MPS file data.
readMPSFile :: FileOptions -> FilePath -> IO (Problem Scientific)
#ifndef WITH_ZLIB
readMPSFile = MPSFile.parseFile
#else
readMPSFile opt fname = do
  s <- readTextFile opt fname
  let ret = MPSFile.parseString opt fname s
  case ret of
    Left e -> throw e
    Right a -> return a
#endif

readTextFile :: FileOptions -> FilePath -> IO TL.Text
#ifndef WITH_ZLIB
readTextFile opt fname = do
  h <- openFile fname ReadMode
  case MIP.optFileEncoding opt of
    Nothing -> return ()
    Just enc -> hSetEncoding h enc
  TLIO.hGetContents h
#else
readTextFile opt fname = do
  enc <- case optFileEncoding opt of
         Nothing -> getLocaleEncoding
         Just enc -> return enc
  let f = if CI.mk (takeExtension fname) == ".gz" then GZip.decompress else id
  s <- BL.readFile fname
  return $ decode enc $ f s
#endif

-- | Parse a string containing LP file data.
parseLPString :: FileOptions -> String -> String -> Either (ParseError String) (Problem Scientific)
parseLPString = LPFile.parseString

-- | Parse a string containing MPS file data.
parseMPSString :: FileOptions -> String -> String -> Either (ParseError String) (Problem Scientific)
parseMPSString = MPSFile.parseString

writeFile :: FileOptions -> FilePath -> Problem Scientific -> IO ()
writeFile opt fname prob =
  case getExt fname of
    ".lp"  -> writeLPFile opt fname prob
    ".mps" -> writeMPSFile opt fname prob
    ext -> ioError $ userError $ "unknown extension: " ++ ext

getExt :: String -> String
getExt name | (base, ext) <- splitExtension name =
  case map toLower ext of
#ifdef WITH_ZLIB
    ".gz" -> getExt base
#endif
    s -> s

writeLPFile :: FileOptions -> FilePath -> Problem Scientific -> IO ()
writeLPFile opt fname prob =
  case LPFile.render opt prob of
    Left err -> ioError $ userError err
    Right s -> writeTextFile opt fname s

writeMPSFile :: FileOptions -> FilePath -> Problem Scientific -> IO ()
writeMPSFile opt fname prob =
  case MPSFile.render opt prob of
    Left err -> ioError $ userError err
    Right s -> writeTextFile opt fname s

writeTextFile :: FileOptions -> FilePath -> TL.Text -> IO ()
writeTextFile opt fname s = do
  let writeSimple = do
        withFile fname WriteMode $ \h -> do
          case optFileEncoding opt of
            Nothing -> return ()
            Just enc -> hSetEncoding h enc
          TLIO.hPutStr h s
#ifdef WITH_ZLIB
  if CI.mk (takeExtension fname) /= ".gz" then do
    writeSimple
  else do
    enc <- case optFileEncoding opt of
             Nothing -> getLocaleEncoding
             Just enc -> return enc
    BL.writeFile fname $ GZip.compress $ encode enc s
#else
  writeSimple
#endif

toLPString :: FileOptions -> Problem Scientific -> Either String TL.Text
toLPString = LPFile.render

toMPSString :: FileOptions -> Problem Scientific -> Either String TL.Text
toMPSString = MPSFile.render
