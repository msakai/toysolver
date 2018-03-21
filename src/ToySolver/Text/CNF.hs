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
  { cnfNumVars :: !Int
  , cnfNumClauses :: !Int
  , cnfClauses :: [SAT.PackedClause]
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
        { cnfNumVars    = read $ BS.unpack nvar
        , cnfNumClauses = read $ BS.unpack nclause
        , cnfClauses    = map parseClauseBS ls
        }
    _ ->
      Left "cannot find cnf header"
  where
    l :: BS.ByteString
    ls :: [BS.ByteString]
    (l:ls) = filter (not . isCommentBS) (BS.lines s)

parseClauseBS :: BS.ByteString -> SAT.PackedClause
parseClauseBS s = SAT.packClause (go s)
  where
    go s =
      case BS.readInt (BS.dropWhile isSpace s) of
        Nothing -> error "ToySolver.Text.CNF: parse error"
        Just (0,_) -> []
        Just (i,s') -> i : go s'

isCommentBS :: BS.ByteString -> Bool
isCommentBS s =
  case BS.uncons s of
    Just ('c',_) ->  True
    _ -> False

writeFile :: FilePath -> CNF -> IO ()
writeFile filepath cnf = do
  withBinaryFile filepath WriteMode $ \h -> do
    hSetBuffering h (BlockBuffering Nothing)
    hPutCNF h cnf

cnfBuilder :: CNF -> Builder
cnfBuilder cnf = header <> mconcat (map f (cnfClauses cnf))
  where
    header = mconcat
      [ byteString "p cnf "
      , intDec (cnfNumVars cnf), char7 ' '
      , intDec (cnfNumClauses cnf), char7 '\n'
      ]
    f c = mconcat [intDec lit <> char7 ' '| lit <- SAT.unpackClause c] <> byteString "0\n"

hPutCNF :: Handle -> CNF -> IO ()
hPutCNF h cnf = hPutBuilder h (cnfBuilder cnf)
