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
  -- * FileFormat class
    FileFormat (..)
  , parseFile
  , writeFile

  -- * DIMACS CNF format
  , CNF (..)
  , hPutCNF
  , cnfBuilder

  -- * WCNF format for weighted MAX-SAT problems
  --
  -- $WCNF
  , WCNF (..)
  , WeightedClause
  , Weight
  , hPutWCNF
  , wcnfBuilder

  -- * GCNF format for Group oriented MUS problems
  --
  -- $GCNF
  , GCNF (..)
  , GroupIndex
  , GClause
  , hPutGCNF
  , gcnfBuilder
  ) where

import Prelude hiding (writeFile)
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.ByteString.Builder
import Data.Char
import Data.Monoid
import System.IO hiding (writeFile)

import qualified ToySolver.SAT.Types as SAT

-- -------------------------------------------------------------------

class FileFormat a where
  parseByteString :: BS.ByteString -> Either String a
  render :: a -> Builder

parseFile :: FileFormat a => FilePath -> IO (Either String a)
parseFile filename = do
  s <- BS.readFile filename
  return $ parseByteString s

writeFile :: FileFormat a => FilePath -> a -> IO ()
writeFile filepath a = do
  withBinaryFile filepath WriteMode $ \h -> do
    hSetBuffering h (BlockBuffering Nothing)
    hPutBuilder h (render a)

-- -------------------------------------------------------------------

data CNF
  = CNF
  { cnfNumVars :: !Int
  , cnfNumClauses :: !Int
  , cnfClauses :: [SAT.PackedClause]
  }
  deriving (Show, Eq, Ord)

instance FileFormat CNF where
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

  render cnf = header <> mconcat (map f (cnfClauses cnf))
    where
      header = mconcat
        [ byteString "p cnf "
        , intDec (cnfNumVars cnf), char7 ' '
        , intDec (cnfNumClauses cnf), char7 '\n'
        ]
      f c = mconcat [intDec lit <> char7 ' '| lit <- SAT.unpackClause c] <> byteString "0\n"

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

cnfBuilder :: CNF -> Builder
cnfBuilder = render

hPutCNF :: Handle -> CNF -> IO ()
hPutCNF h cnf = hPutBuilder h (cnfBuilder cnf)

-- -------------------------------------------------------------------

-- $WCNF
--
-- References:
--
-- * <http://maxsat.ia.udl.cat/requirements/>

data WCNF
  = WCNF
  { wcnfNumVars    :: !Int
  , wcnfNumClauses :: !Int
  , wcnfTopCost    :: !Weight
  , wcnfClauses    :: [WeightedClause]
  }
  deriving (Show, Eq, Ord)

type WeightedClause = (Weight, SAT.PackedClause)

-- | Weigths must be greater than or equal to 1, and smaller than 2^63.
type Weight = Integer

instance FileFormat WCNF where
  parseByteString s =
    case BS.words l of
      (["p","wcnf", nvar, nclause, top]) ->
        Right $
          WCNF
          { wcnfNumVars    = read $ BS.unpack nvar
          , wcnfNumClauses = read $ BS.unpack nclause
          , wcnfTopCost    = read $ BS.unpack top
          , wcnfClauses    = map parseWCNFLineBS ls
          }
      (["p","wcnf", nvar, nclause]) ->
        Right $
          WCNF
          { wcnfNumVars    = read $ BS.unpack nvar
          , wcnfNumClauses = read $ BS.unpack nclause
            -- top must be greater than the sum of the weights of violated soft clauses.
          , wcnfTopCost    = fromInteger $ 2^(63::Int) - 1
          , wcnfClauses    = map parseWCNFLineBS ls
          }
      (["p","cnf", nvar, nclause]) ->
        Right $
          WCNF
          { wcnfNumVars    = read $ BS.unpack nvar
          , wcnfNumClauses = read $ BS.unpack nclause
            -- top must be greater than the sum of the weights of violated soft clauses.
          , wcnfTopCost    = fromInteger $ 2^(63::Int) - 1
          , wcnfClauses    = map ((\c -> seq c (1,c)) . parseClauseBS)  ls
          }
      _ ->
        Left "cannot find wcnf/cnf header"
    where
      l :: BS.ByteString
      ls :: [BS.ByteString]
      (l:ls) = filter (not . isCommentBS) (BS.lines s)

  render wcnf = header <> mconcat (map f (wcnfClauses wcnf))
    where
      header = mconcat
        [ byteString "p wcnf "
        , intDec (wcnfNumVars wcnf), char7 ' '
        , intDec (wcnfNumClauses wcnf), char7 ' '
        , integerDec (wcnfTopCost wcnf), char7 '\n'
        ]
      f (w,c) = integerDec w <> mconcat [char7 ' ' <> intDec lit | lit <- SAT.unpackClause c] <> byteString " 0\n"

parseWCNFLineBS :: BS.ByteString -> WeightedClause
parseWCNFLineBS s =
  case BS.readInteger (BS.dropWhile isSpace s) of
    Nothing -> error "ToySolver.Text.CNF: no weight"
    Just (w, s') -> seq w $ seq xs $ (w, xs)
      where
        xs = parseClauseBS s'

wcnfBuilder :: WCNF -> Builder
wcnfBuilder = render

hPutWCNF :: Handle -> WCNF -> IO ()
hPutWCNF h wcnf = hPutBuilder h (wcnfBuilder wcnf)

-- -------------------------------------------------------------------

-- $GCNF
--
-- References:
--
-- * <http://www.satcompetition.org/2011/rules.pdf>

data GCNF
  = GCNF
  { gcnfNumVars        :: !Int
  , gcnfNumClauses     :: !Int
  , gcnfLastGroupIndex :: !GroupIndex
  , gcnfClauses        :: [GClause]
  }
  deriving (Eq, Ord, Show, Read)

type GroupIndex = Int

type GClause = (GroupIndex, SAT.PackedClause)

instance FileFormat GCNF where
  parseByteString s =
    case BS.words l of
      (["p","gcnf", nbvar', nbclauses', lastGroupIndex']) ->
        Right $
          GCNF
          { gcnfNumVars        = read $ BS.unpack nbvar'
          , gcnfNumClauses     = read $ BS.unpack nbclauses'
          , gcnfLastGroupIndex = read $ BS.unpack lastGroupIndex'
          , gcnfClauses        = map parseGCNFLineBS ls
          }
      (["p","cnf", nbvar', nbclause']) ->
        Right $
          GCNF
          { gcnfNumVars        = read $ BS.unpack nbvar'
          , gcnfNumClauses     = read $ BS.unpack nbclause'
          , gcnfLastGroupIndex = read $ BS.unpack nbclause'
          , gcnfClauses        = zip [1..] $ map parseClauseBS ls
          }
      _ ->
        Left "cannot find gcnf header"
    where
      l :: BS.ByteString
      ls :: [BS.ByteString]
      (l:ls) = filter (not . isCommentBS) (BS.lines s)

  render gcnf = header <> mconcat (map f (gcnfClauses gcnf))
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

parseGCNFLineBS :: BS.ByteString -> GClause
parseGCNFLineBS s =
  case BS.uncons (BS.dropWhile isSpace s) of
    Just ('{', s1) ->
      case BS.readInt s1 of
        Just (idx,s2) | Just ('}', s3) <- BS.uncons s2 ->
          let ys = parseClauseBS s3
          in seq idx $ seq ys $ (idx, ys)
        _ -> error "ToySolver.Text.CNF: parse error"
    _ -> error "ToySolver.Text.CNF: parse error"

gcnfBuilder :: GCNF -> Builder
gcnfBuilder = render

hPutGCNF :: Handle -> GCNF -> IO ()
hPutGCNF h gcnf = hPutBuilder h (gcnfBuilder gcnf)

-- -------------------------------------------------------------------
