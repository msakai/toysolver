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
  , parseString
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
  { numVars        :: !Int
  , numClauses     :: !Int
  , lastGroupIndex :: !GroupIndex
  , clauses        :: [GClause]
  }

type GroupIndex = Int

type GClause = (GroupIndex, SAT.Clause)

parseString :: String -> Either String GCNF
parseString s =
  case words l of
    (["p","gcnf", nbvar', nbclauses', lastGroupIndex']) ->
      Right $
        GCNF
        { numVars        = read nbvar'
        , numClauses     = read nbclauses'
        , lastGroupIndex = read lastGroupIndex'
        , clauses        = map parseLine ls
        }
    (["p","cnf", nbvar', nbclause']) ->
      Right $
        GCNF
        { numVars        = read nbvar'
        , numClauses     = read nbclause'
        , lastGroupIndex = read nbclause'
        , clauses        = zip [1..] $ map parseCNFLine ls
        }
    _ ->
      Left "cannot find gcnf header"
  where
    (l:ls) = filter (not . isComment) (lines s)

parseFile :: FilePath -> IO (Either String GCNF)
parseFile filename = do
  -- s <- readFile filename
  -- return $ parseString s
  s <- BS.readFile filename
  return $ parseByteString s

isComment :: String -> Bool
isComment ('c':_) = True
isComment _ = False

parseLine :: String -> GClause
parseLine s =
  case words s of
    (('{':w):xs) ->
        let ys  = map readInt $ init xs
            idx = readInt $ init w
        in seq idx $ seqList ys $ (idx, ys)
    _ -> error "ToySolver.Text.GCNF: parse error"

parseCNFLine :: String -> SAT.Clause
parseCNFLine s = seq xs $ seqList xs $ xs
  where
    xs = init (map readInt (words s))

parseByteString :: BS.ByteString -> Either String GCNF
parseByteString s =
  case BS.words l of
    (["p","gcnf", nbvar', nbclauses', lastGroupIndex']) ->
      Right $
        GCNF
        { numVars        = read $ BS.unpack nbvar'
        , numClauses     = read $ BS.unpack nbclauses'
        , lastGroupIndex = read $ BS.unpack lastGroupIndex'
        , clauses        = map parseLineBS ls
        }
    (["p","cnf", nbvar', nbclause']) ->
      Right $
        GCNF
        { numVars        = read $ BS.unpack nbvar'
        , numClauses     = read $ BS.unpack nbclause'
        , lastGroupIndex = read $ BS.unpack nbclause'
        , clauses        = zip [1..] $ map parseCNFLineBS ls
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
          in seq idx $ seqList ys $ (idx, ys)
        _ -> error "ToySolver.Text.GCNF: parse error"
    _ -> error "ToySolver.Text.GCNF: parse error"

parseCNFLineBS :: BS.ByteString -> SAT.Clause
parseCNFLineBS s = seq xs $ seqList xs $ xs
  where
    xs = parseClauseBS s

parseClauseBS :: BS.ByteString -> SAT.Clause
parseClauseBS s = seqList xs $ xs
  where
    xs = go s
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

seqList :: [a] -> b -> b
seqList [] b = b
seqList (x:xs) b = seq x $ seqList xs b

writeFile :: FilePath -> GCNF -> IO ()
writeFile filepath gcnf = do
  withBinaryFile filepath WriteMode $ \h -> do
    hSetBuffering h (BlockBuffering Nothing)
    hPutGCNF h gcnf

gcnfBuilder :: GCNF -> Builder
gcnfBuilder gcnf = header <> mconcat (map f (clauses gcnf))
  where
    header = mconcat
      [ byteString "p gcnf "
      , intDec (numVars gcnf), char7 ' '
      , intDec (numClauses gcnf), char7 ' '
      , intDec (lastGroupIndex gcnf), char7 '\n'
      ]
    f (idx,c) = char7 '{' <> intDec idx <> char7 '}' <>
                mconcat [char7 ' ' <> intDec lit | lit <- c] <>
                byteString " 0\n"

hPutGCNF :: Handle -> GCNF -> IO ()
hPutGCNF h gcnf = hPutBuilder h (gcnfBuilder gcnf)
