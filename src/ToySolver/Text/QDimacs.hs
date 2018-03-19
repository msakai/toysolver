{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.QDimacs
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- References:
--
-- * QDIMACS standard Ver. 1.1
--   <http://www.qbflib.org/qdimacs.html>
--
-----------------------------------------------------------------------------
module ToySolver.Text.QDimacs
  ( QDimacs (..)
  , Quantifier (..)
  , QuantSet
  , Atom
  , Lit
  , Clause
  , PackedClause
  , packClause
  , unpackClause
  , parseFile
  , parseByteString

  -- * Generating .qdimacs files
  , writeFile
  , hPutQDimacs
  , qdimacsBuilder
  ) where

import Prelude hiding (writeFile)
-- import Control.Applicative
import Control.DeepSeq
import Data.ByteString.Builder
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.Char
import Data.Monoid
import System.IO hiding (writeFile)
import qualified ToySolver.SAT.Types as SAT
import ToySolver.SAT.Types (Clause, Lit, PackedClause, packClause, unpackClause)

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
  { numVars :: !Int
  , numClauses :: !Int
  , prefix :: [QuantSet]
  , matrix :: [PackedClause]
  }
  deriving (Eq, Ord, Show, Read)

data Quantifier
  = E -- ^ existential quantifier
  | A -- ^ universal quantifier
  deriving (Eq, Ord, Show, Read, Enum, Bounded)

type QuantSet = (Quantifier, [Atom])

type Atom = SAT.Var

parseFile :: FilePath -> IO (Either String QDimacs)
parseFile filename = do
  s <- BL.readFile filename
  return $ parseByteString s

parseByteString :: BL.ByteString -> (Either String QDimacs)
parseByteString = f . BL.lines
  where
    f [] = Left "QDimacs.parseByteString: premature end of file"
    f (l : ls) =
      case BL.uncons l of
        Nothing -> Left "QDimacs.parseByteString: no problem line"
        Just ('c', _) -> f ls
        Just ('p', s) ->
          case BL.words s of
            ["cnf", numVars', numClauses'] ->
              case parsePrefix ls of
                (prefix', ls') -> Right $
                  QDimacs
                  { numVars = read $ BL.unpack numVars'
                  , numClauses = read $ BL.unpack numClauses'
                  , prefix = prefix'
                  , matrix = map parseClause ls'
                  }
            _ -> Left "QDimacs.parseByteString: invalid problem line"
        Just (c, _) -> Left ("QDimacs.parseByteString: invalid prefix " ++ show c)

parsePrefix :: [BL.ByteString] -> ([QuantSet], [BL.ByteString])
parsePrefix = go []
  where
    go result [] = (reverse result, [])
    go result lls@(l : ls) =
      case BL.uncons l of
        Just (c,s)
          | c=='a' || c=='e' ->
              let atoms = readInts s
                  q = if c=='a' then A else E
              in seq q $ deepseq atoms $ go ((q, atoms) : result) ls
          | otherwise ->
              (reverse result, lls)
        _ -> error "QDimacs.parseProblem: invalid line"

parseClause :: BL.ByteString -> SAT.PackedClause
parseClause = SAT.packClause . readInts

readInts :: BL.ByteString -> [Int]
readInts s =
  case BL.readInt (BL.dropWhile isSpace s) of
    Just (0,_) -> []
    Just (z,s') -> z : readInts s'
    Nothing -> error "QDimacs.readInts: 0 is missing"


writeFile :: FilePath -> QDimacs -> IO ()
writeFile filepath qdimacs = do
  withBinaryFile filepath WriteMode $ \h -> do
    hSetBuffering h (BlockBuffering Nothing)
    hPutBuilder h (qdimacsBuilder qdimacs)

qdimacsBuilder :: QDimacs -> Builder
qdimacsBuilder qdimacs = problem_line <> prefix' <> mconcat (map f (matrix qdimacs))
  where
    problem_line = mconcat
      [ byteString "p cnf "
      , intDec (numVars qdimacs), char7 ' '
      , intDec (numClauses qdimacs), char7 '\n'
      ]
    prefix' = mconcat
      [ char7 (if q == E then 'e' else 'a') <> mconcat [char7 ' ' <> intDec atom | atom <- atoms] <> byteString " 0\n"
      | (q, atoms) <- prefix qdimacs
      ]
    f c = mconcat [intDec lit <> char7 ' '| lit <- SAT.unpackClause c] <> byteString "0\n"

hPutQDimacs :: Handle -> QDimacs -> IO ()
hPutQDimacs h qdimacs = hPutBuilder h (qdimacsBuilder qdimacs)
