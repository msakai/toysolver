{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.WCNF
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
-- 
-- References:
-- 
-- * <http://maxsat.ia.udl.cat/requirements/>
--
-----------------------------------------------------------------------------
module ToySolver.Text.WCNF
  (
    WCNF (..)
  , WeightedClause
  , Weight

  -- * Parsing .cnf/.wcnf files
  , parseFile
  , parseByteString

  -- * Generating .wcnf files
  , writeFile
  , hPutWCNF
  , wcnfBuilder
  ) where

import Prelude hiding (writeFile)
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.ByteString.Builder
import Data.Char
import Data.Monoid
import System.IO hiding (writeFile)

import qualified ToySolver.SAT.Types as SAT
import ToySolver.Internal.TextUtil

data WCNF
  = WCNF
  { numVars    :: !Int
  , numClauses :: !Int
  , topCost    :: !Weight
  , clauses    :: [WeightedClause]
  }
  deriving (Show, Eq, Ord)

type WeightedClause = (Weight, SAT.PackedClause)

-- | Weigths must be greater than or equal to 1, and smaller than 2^63.
type Weight = Integer

parseFile :: FilePath -> IO (Either String WCNF)
parseFile filename = do
  s <- BS.readFile filename
  return $ parseByteString s

parseByteString :: BS.ByteString -> Either String WCNF
parseByteString s =
  case BS.words l of
    (["p","wcnf", nvar, nclause, top]) ->
      Right $
        WCNF
        { numVars    = read $ BS.unpack nvar
        , numClauses = read $ BS.unpack nclause
        , topCost    = read $ BS.unpack top
        , clauses    = map parseWCNFLineBS ls
        }
    (["p","wcnf", nvar, nclause]) ->
      Right $
        WCNF
        { numVars    = read $ BS.unpack nvar
        , numClauses = read $ BS.unpack nclause
          -- top must be greater than the sum of the weights of violated soft clauses.
        , topCost    = fromInteger $ 2^(63::Int) - 1
        , clauses    = map parseWCNFLineBS ls
        }
    (["p","cnf", nvar, nclause]) ->
      Right $
        WCNF
        { numVars    = read $ BS.unpack nvar
        , numClauses = read $ BS.unpack nclause
          -- top must be greater than the sum of the weights of violated soft clauses.
        , topCost    = fromInteger $ 2^(63::Int) - 1
        , clauses    = map parseCNFLineBS ls
        }
    _ ->
      Left "cannot find wcnf/cnf header"
  where
    l :: BS.ByteString
    ls :: [BS.ByteString]
    (l:ls) = filter (not . isCommentBS) (BS.lines s)

parseWCNFLineBS :: BS.ByteString -> WeightedClause
parseWCNFLineBS s =
  case BS.readInteger (BS.dropWhile isSpace s) of
    Nothing -> error "ToySolver.Text.WCNF: no weight"
    Just (w, s') -> seq w $ seq xs $ (w, xs)
      where
        xs = parseClauseBS s'

parseCNFLineBS :: BS.ByteString -> WeightedClause
parseCNFLineBS s = seq xs $ (1, xs)
  where
    xs = parseClauseBS s

parseClauseBS :: BS.ByteString -> SAT.PackedClause
parseClauseBS s = SAT.packClause (go s)
  where
    go s =
      case BS.readInt (BS.dropWhile isSpace s) of
        Nothing -> error "ToySolver.Text.WCNF: parse error"
        Just (0,_) -> []
        Just (i,s') -> i : go s'

isCommentBS :: BS.ByteString -> Bool
isCommentBS s =
  case BS.uncons s of
    Just ('c',_) ->  True
    _ -> False

writeFile :: FilePath -> WCNF -> IO ()
writeFile filepath wcnf = do
  withBinaryFile filepath WriteMode $ \h -> do
    hSetBuffering h (BlockBuffering Nothing)
    hPutWCNF h wcnf

wcnfBuilder :: WCNF -> Builder
wcnfBuilder wcnf = header <> mconcat (map f (clauses wcnf))
  where
    header = mconcat
      [ byteString "p wcnf "
      , intDec (numVars wcnf), char7 ' '
      , intDec (numClauses wcnf), char7 ' '
      , integerDec (topCost wcnf), char7 '\n'
      ]
    f (w,c) = integerDec w <> mconcat [char7 ' ' <> intDec lit | lit <- SAT.unpackClause c] <> byteString " 0\n"

hPutWCNF :: Handle -> WCNF -> IO ()
hPutWCNF h wcnf = hPutBuilder h (wcnfBuilder wcnf)
