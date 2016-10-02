{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.CNF
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (FlexibleContexts, OverloadedStrings)
--
-----------------------------------------------------------------------------
module ToySolver.Text.CNF
  (
    CNF (..)

  -- * Parsing .cnf files
  , parseFile
  , parseByteString

  -- * Generating .cnf files
  , writeFile
  , hPutCNF
  , cnfBuilder
  ) where

import Prelude hiding (writeFile)
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.ByteString.Builder
import Data.Char
import Data.Monoid
import System.IO hiding (writeFile)

import qualified ToySolver.SAT.Types as SAT

data CNF
  = CNF
  { numVars :: !Int
  , numClauses :: !Int
  , clauses :: [SAT.Clause]
  }
  deriving (Show, Eq, Ord)

parseFile :: FilePath -> IO (Either String CNF)
parseFile filename = do
  s <- BS.readFile filename
  return $ parseByteString s

parseByteString :: BS.ByteString -> Either String CNF
parseByteString s =
  case BS.words l of
    (["p","cnf", nvar, nclause]) ->
      Right $
        CNF
        { numVars    = read $ BS.unpack nvar
        , numClauses = read $ BS.unpack nclause
        , clauses    = map parseClauseBS ls
        }
    _ ->
      Left "cannot find cnf header"
  where
    l :: BS.ByteString
    ls :: [BS.ByteString]
    (l:ls) = filter (not . isCommentBS) (BS.lines s)

parseClauseBS :: BS.ByteString -> SAT.Clause
parseClauseBS s = seqList xs $ xs
  where
    xs = go s
    go s =
      case BS.readInt (BS.dropWhile isSpace s) of
        Nothing -> error "ToySolver.Text.MaxSAT: parse error"
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

writeFile :: FilePath -> CNF -> IO ()
writeFile filepath cnf = do
  withBinaryFile filepath WriteMode $ \h -> do
    hSetBuffering h (BlockBuffering Nothing)
    hPutBuilder h (cnfBuilder cnf)

cnfBuilder :: CNF -> Builder
cnfBuilder cnf = header <> mconcat (map f (clauses cnf))
  where
    header = mconcat
      [ byteString "p cnf "
      , intDec (numVars cnf), char7 ' '
      , intDec (numClauses cnf), char7 '\n'
      ]
    f c = mconcat [intDec lit <> char7 ' '| lit <- c] <> byteString "0\n"

hPutCNF :: Handle -> CNF -> IO ()
hPutCNF h cnf = hPutBuilder h (cnfBuilder cnf)
