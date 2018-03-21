{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.GCNF
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (OverloadedStrings)
-- 
-- References:
-- 
-- * <http://www.satcompetition.org/2011/rules.pdf>
--
--
-----------------------------------------------------------------------------
module ToySolver.Text.GCNF
  (
    GCNF (..)
  , GroupIndex
  , GClause

  -- * Parsing .gcnf files
  , parseByteString
  , parseFile

  -- * Generating .gcnf files
  , writeFile
  , hPutGCNF
  , gcnfBuilder
  ) where

import Prelude hiding (writeFile)
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.ByteString.Builder
import Data.Char
import Data.Monoid
import qualified ToySolver.SAT.Types as SAT
import System.IO hiding (writeFile)
import ToySolver.Internal.TextUtil

data GCNF
  = GCNF
  { gcnfNumVars        :: !Int
  , gcnfNumClauses     :: !Int
  , gcnfLastGroupIndex :: !GroupIndex
  , gcnfClauses        :: [GClause]
  }

type GroupIndex = Int

type GClause = (GroupIndex, SAT.PackedClause)


parseFile :: FilePath -> IO (Either String GCNF)
parseFile filename = do
  s <- BS.readFile filename
  return $ parseByteString s

parseByteString :: BS.ByteString -> Either String GCNF
parseByteString s =
  case BS.words l of
    (["p","gcnf", nbvar', nbclauses', lastGroupIndex']) ->
      Right $
        GCNF
        { gcnfNumVars        = read $ BS.unpack nbvar'
        , gcnfNumClauses     = read $ BS.unpack nbclauses'
        , gcnfLastGroupIndex = read $ BS.unpack lastGroupIndex'
        , gcnfClauses        = map parseLineBS ls
        }
    (["p","cnf", nbvar', nbclause']) ->
      Right $
        GCNF
        { gcnfNumVars        = read $ BS.unpack nbvar'
        , gcnfNumClauses     = read $ BS.unpack nbclause'
        , gcnfLastGroupIndex = read $ BS.unpack nbclause'
        , gcnfClauses        = zip [1..] $ map parseCNFLineBS ls
        }
    _ ->
      Left "cannot find gcnf header"
  where
    l :: BS.ByteString
    ls :: [BS.ByteString]
    (l:ls) = filter (not . isCommentBS) (BS.lines s)
    
parseLineBS :: BS.ByteString -> GClause
parseLineBS s =
  case BS.uncons (BS.dropWhile isSpace s) of
    Just ('{', s1) ->
      case BS.readInt s1 of
        Just (idx,s2) | Just ('}', s3) <- BS.uncons s2 -> 
          let ys = parseClauseBS s3
          in seq idx $ seq ys $ (idx, ys)
        _ -> error "ToySolver.Text.GCNF: parse error"
    _ -> error "ToySolver.Text.GCNF: parse error"

parseCNFLineBS :: BS.ByteString -> SAT.PackedClause
parseCNFLineBS s = parseClauseBS s

parseClauseBS :: BS.ByteString -> SAT.PackedClause
parseClauseBS s = SAT.packClause (go s)
  where
    go s =
      case BS.readInt (BS.dropWhile isSpace s) of
        Nothing -> error "ToySolver.Text.GCNF: parse error"
        Just (0,_) -> []
        Just (i,s') -> i : go s'

isCommentBS :: BS.ByteString -> Bool
isCommentBS s =
  case BS.uncons s of
    Just ('c',_) ->  True
    _ -> False

writeFile :: FilePath -> GCNF -> IO ()
writeFile filepath gcnf = do
  withBinaryFile filepath WriteMode $ \h -> do
    hSetBuffering h (BlockBuffering Nothing)
    hPutGCNF h gcnf

gcnfBuilder :: GCNF -> Builder
gcnfBuilder gcnf = header <> mconcat (map f (gcnfClauses gcnf))
  where
    header = mconcat
      [ byteString "p gcnf "
      , intDec (gcnfNumVars gcnf), char7 ' '
      , intDec (gcnfNumClauses gcnf), char7 ' '
      , intDec (gcnfLastGroupIndex gcnf), char7 '\n'
      ]
    f (idx,c) = char7 '{' <> intDec idx <> char7 '}' <>
                mconcat [char7 ' ' <> intDec lit | lit <- SAT.unpackClause c] <>
                byteString " 0\n"

hPutGCNF :: Handle -> GCNF -> IO ()
hPutGCNF h gcnf = hPutBuilder h (gcnfBuilder gcnf)
