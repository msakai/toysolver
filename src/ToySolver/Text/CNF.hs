{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.CNF
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Text.CNF
  (
  -- * FileFormat class
    FileFormat (..)
  , ParseError (..)
  , parseFile
  , readFile
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

  -- * QDIMACS format
  --
  -- $QDIMACS
  , QDimacs (..)
  , Quantifier (..)
  , QuantSet
  , Atom
  , hPutQDimacs
  , qdimacsBuilder

  -- * Re-exports
  , Lit
  , Clause
  , PackedClause
  , packClause
  , unpackClause
  ) where

import Prelude hiding (readFile, writeFile)
import Control.DeepSeq
import Control.Exception
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.ByteString.Builder
import Data.Char
import Data.Monoid
import Data.Typeable
import System.IO hiding (readFile, writeFile)

import qualified ToySolver.SAT.Types as SAT
import ToySolver.SAT.Types (Lit, Clause, PackedClause, packClause, unpackClause)

-- -------------------------------------------------------------------

class FileFormat a where
  parseByteString :: BS.ByteString -> Either String a
  render :: a -> Builder

data ParseError = ParseError String
  deriving (Show, Typeable)

instance Exception ParseError

parseFile :: FileFormat a => FilePath -> IO (Either String a)
parseFile filename = do
  s <- BS.readFile filename
  return $ parseByteString s

readFile :: FileFormat a => FilePath -> IO a
readFile filename = do
  s <- BS.readFile filename
  case parseByteString s of
    Left msg -> throw $ ParseError msg
    Right a -> return a

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
  deriving (Eq, Ord, Show, Read)

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

readInts :: BS.ByteString -> [Int]
readInts s =
  case BS.readInt (BS.dropWhile isSpace s) of
    Just (0,_) -> []
    Just (z,s') -> z : readInts s'
    Nothing -> error "ToySolver.Text.CNF.readInts: 0 is missing"

parseClauseBS :: BS.ByteString -> SAT.PackedClause
parseClauseBS = SAT.packClause . readInts

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
  deriving (Eq, Ord, Show, Read)

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
parseGCNFLineBS s
  | Just ('{', s1) <- BS.uncons (BS.dropWhile isSpace s)
  , Just (!idx,s2) <- BS.readInt s1
  , Just ('}', s3) <- BS.uncons s2 =
      let ys = parseClauseBS s3
      in seq ys $ (idx, ys)
  | otherwise = error "ToySolver.Text.CNF: parse error"

gcnfBuilder :: GCNF -> Builder
gcnfBuilder = render

hPutGCNF :: Handle -> GCNF -> IO ()
hPutGCNF h gcnf = hPutBuilder h (gcnfBuilder gcnf)

-- -------------------------------------------------------------------

-- $QDIMACS
--
-- References:
--
-- * QDIMACS standard Ver. 1.1
--   <http://www.qbflib.org/qdimacs.html>

{-
http://www.qbflib.org/qdimacs.html

<input> ::= <preamble> <prefix> <matrix> EOF

<preamble> ::= [<comment_lines>] <problem_line>
<comment_lines> ::= <comment_line> <comment_lines> | <comment_line>
<comment_line> ::= c <text> EOL
<problem_line> ::= p cnf <pnum> <pnum> EOL

<prefix> ::= [<quant_sets>]
<quant_sets> ::= <quant_set> <quant_sets> | <quant_set>
<quant_set> ::= <quantifier> <atom_set> 0 EOL
<quantifier> ::= e | a
<atom_set> ::= <pnum> <atom_set> | <pnum>

<matrix> ::= <clause_list>
<clause_list> ::= <clause> <clause_list> | <clause>
<clause> ::= <literal> <clause> | <literal> 0 EOL
<literal> ::= <num>

<text> ::= {A sequence of non-special ASCII characters}
<num> ::= {A 32-bit signed integer different from 0}
<pnum> ::= {A 32-bit signed integer greater than 0}
-}

data QDimacs
  = QDimacs
  { qdimacsNumVars :: !Int
  , qdimacsNumClauses :: !Int
  , qdimacsPrefix :: [QuantSet]
  , qdimacsMatrix :: [SAT.PackedClause]
  }
  deriving (Eq, Ord, Show, Read)

data Quantifier
  = E -- ^ existential quantifier
  | A -- ^ universal quantifier
  deriving (Eq, Ord, Show, Read, Enum, Bounded)

type QuantSet = (Quantifier, [Atom])

type Atom = SAT.Var

instance FileFormat QDimacs where
  parseByteString = f . BS.lines
    where
      f [] = Left "ToySolver.Text.CNF.parseByteString: premature end of file"
      f (l : ls) =
        case BS.uncons l of
          Nothing -> Left "ToySolver.Text.CNF.parseByteString: no problem line"
          Just ('c', _) -> f ls
          Just ('p', s) ->
            case BS.words s of
              ["cnf", numVars', numClauses'] ->
                case parsePrefix ls of
                  (prefix', ls') -> Right $
                    QDimacs
                    { qdimacsNumVars = read $ BS.unpack numVars'
                    , qdimacsNumClauses = read $ BS.unpack numClauses'
                    , qdimacsPrefix = prefix'
                    , qdimacsMatrix = map parseClauseBS ls'
                    }
              _ -> Left "ToySolver.Text.CNF.parseByteString: invalid problem line"
          Just (c, _) -> Left ("ToySolver.Text.CNF.parseByteString: invalid prefix " ++ show c)

  render qdimacs = problem_line <> prefix' <> mconcat (map f (qdimacsMatrix qdimacs))
    where
      problem_line = mconcat
        [ byteString "p cnf "
        , intDec (qdimacsNumVars qdimacs), char7 ' '
        , intDec (qdimacsNumClauses qdimacs), char7 '\n'
        ]
      prefix' = mconcat
        [ char7 (if q == E then 'e' else 'a') <> mconcat [char7 ' ' <> intDec atom | atom <- atoms] <> byteString " 0\n"
        | (q, atoms) <- qdimacsPrefix qdimacs
        ]
      f c = mconcat [intDec lit <> char7 ' '| lit <- SAT.unpackClause c] <> byteString "0\n"

parsePrefix :: [BS.ByteString] -> ([QuantSet], [BS.ByteString])
parsePrefix = go []
  where
    go result [] = (reverse result, [])
    go result lls@(l : ls) =
      case BS.uncons l of
        Just (c,s)
          | c=='a' || c=='e' ->
              let atoms = readInts s
                  q = if c=='a' then A else E
              in seq q $ deepseq atoms $ go ((q, atoms) : result) ls
          | otherwise ->
              (reverse result, lls)
        _ -> error "ToySolver.Text.CNF.parseProblem: invalid line"

qdimacsBuilder :: QDimacs -> Builder
qdimacsBuilder = render

hPutQDimacs :: Handle -> QDimacs -> IO ()
hPutQDimacs h qdimacs = hPutBuilder h (qdimacsBuilder qdimacs)

-- -------------------------------------------------------------------
