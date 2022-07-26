{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.FileFormat.Base
-- Copyright   :  (c) Masahiro Sakai 2016-2018
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.FileFormat.Base
  (
  -- * FileFormat class
    FileFormat (..)
  , ParseError (..)
  , parseFile
  , readFile
  , writeFile
  ) where

import Prelude hiding (readFile, writeFile)
import Control.Exception
import Control.Monad.IO.Class
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.ByteString.Builder hiding (writeFile)
import Data.Typeable
import System.IO hiding (readFile, writeFile)

#ifdef WITH_ZLIB
import qualified Codec.Compression.GZip as GZip
import qualified Data.CaseInsensitive as CI
import System.FilePath
#endif

-- | A type class that abstracts file formats
class FileFormat a where
  -- | Parse a lazy byte string, and either returns error message or a parsed value
  parse :: BS.ByteString -> Either String a

  -- | Encode a value into 'Builder'
  render :: a -> Builder

-- | 'ParseError' represents a parse error and it wraps a error message.
data ParseError = ParseError String
  deriving (Show, Typeable)

instance Exception ParseError

-- | Parse a file but returns an error message when parsing fails.
parseFile :: (FileFormat a, MonadIO m) => FilePath -> m (Either String a)
parseFile filename = liftIO $ do
  s <- BS.readFile filename
#ifdef WITH_ZLIB
  let s2 = if CI.mk (takeExtension filename) == ".gz" then
             GZip.decompress s
           else
             s
#else
  let s2 = s
#endif
  return $ parse s2

-- | Parse a file. Similar to 'parseFile' but this function throws 'ParseError' when parsing fails.
readFile :: (FileFormat a, MonadIO m) => FilePath -> m a
readFile filename = liftIO $ do
  ret <- parseFile filename
  case ret of
    Left msg -> throwIO $ ParseError msg
    Right a -> return a

-- | Write a value into a file.
writeFile :: (FileFormat a, MonadIO m) => FilePath -> a -> m ()
writeFile filepath a = liftIO $ do
  withBinaryFile filepath WriteMode $ \h -> do
    hSetBuffering h (BlockBuffering Nothing)
#ifdef WITH_ZLIB
    if CI.mk (takeExtension filepath) == ".gz" then do
      BS.hPut h $ GZip.compress $ toLazyByteString $ render a
    else do
      hPutBuilder h (render a)
#else
    hPutBuilder h (render a)
#endif
