{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.FileFormat.CNF
-- Copyright   :  (c) Masahiro Sakai 2016-2018
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Reader and Writer for DIMACS CNF and family of similar formats.
--
-----------------------------------------------------------------------------
module ToySolver.FileFormat.CNF
  (
  -- * FileFormat class
    module ToySolver.FileFormat.Base

  -- * CNF format
  , CNF (..)

  -- * WCNF format
  , WCNF (..)
  , WeightedClause
  , Weight

  -- * GCNF format
  , GCNF (..)
  , GroupIndex
  , GClause

  -- * QDIMACS format
  , QDimacs (..)
  , Quantifier (..)
  , QuantSet
  , Atom

  -- * Re-exports
  , Lit
  , Clause
  , PackedClause
  , packClause
  , unpackClause
  ) where

import Prelude hiding (readFile, writeFile)
import Control.DeepSeq
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.ByteString.Builder
import Data.Char
#if !MIN_VERSION_base(4,11,0)
import Data.Monoid
#endif

import ToySolver.FileFormat.Base
import qualified ToySolver.SAT.Types as SAT
import ToySolver.SAT.Types (Lit, Clause, PackedClause, packClause, unpackClause)

-- -------------------------------------------------------------------

-- | DIMACS CNF format
data CNF
  = CNF
  { cnfNumVars :: !Int
    -- ^ Number of variables
  , cnfNumClauses :: !Int
    -- ^ Number of clauses
  , cnfClauses :: [SAT.PackedClause]
    -- ^ Clauses
  }
  deriving (Eq, Ord, Show, Read)

instance FileFormat CNF where
  parse s =
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
    Nothing -> error "ToySolver.FileFormat.CNF.readInts: 0 is missing"

parseClauseBS :: BS.ByteString -> SAT.PackedClause
parseClauseBS = SAT.packClause . readInts

isCommentBS :: BS.ByteString -> Bool
isCommentBS s =
  case BS.uncons s of
    Just ('c',_) ->  True
    _ -> False

-- -------------------------------------------------------------------

-- | WCNF format for representing partial weighted Max-SAT problems.
--
-- This format is used for for MAX-SAT evaluations.
--
-- References:
--
-- * <http://maxsat.ia.udl.cat/requirements/>
data WCNF
  = WCNF
  { wcnfNumVars    :: !Int
    -- ^ Number of variables
  , wcnfNumClauses :: !Int
    -- ^ Number of (weighted) clauses
  , wcnfTopCost    :: !Weight
    -- ^ Hard clauses have weight equal or greater than "top". 
    -- We assure that "top" is a weight always greater than the sum of the weights of violated soft clauses in the solution.
  , wcnfClauses    :: [WeightedClause]
    -- ^ Weighted clauses
  }
  deriving (Eq, Ord, Show, Read)

-- | Weighted clauses
type WeightedClause = (Weight, SAT.PackedClause)

-- | Weigths must be greater than or equal to 1, and smaller than 2^63.
type Weight = Integer

instance FileFormat WCNF where
  parse s =
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
    Nothing -> error "ToySolver.FileFormat.CNF: no weight"
    Just (w, s') -> seq w $ seq xs $ (w, xs)
      where
        xs = parseClauseBS s'

-- -------------------------------------------------------------------

-- | Group oriented CNF Input Format
--
-- This format is used in Group oriented MUS track of the SAT Competition 2011.
--
-- References:
--
-- * <http://www.satcompetition.org/2011/rules.pdf>
data GCNF
  = GCNF
  { gcnfNumVars        :: !Int
    -- ^ Nubmer of variables
  , gcnfNumClauses     :: !Int
    -- ^ Number of clauses
  , gcnfLastGroupIndex :: !GroupIndex
    -- ^ The last index of a group in the file number of components contained in the file.
  , gcnfClauses        :: [GClause]
  }
  deriving (Eq, Ord, Show, Read)

-- | Component number between 0 and `gcnfLastGroupIndex`
type GroupIndex = Int

-- | Clause together with component number
type GClause = (GroupIndex, SAT.PackedClause)

instance FileFormat GCNF where
  parse s =
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
  | otherwise = error "ToySolver.FileFormat.CNF: parse error"

-- -------------------------------------------------------------------

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

-- | QDIMACS format
--
-- Quantified boolean expression in prenex normal form,
-- consisting of a sequence of quantifiers ('qdimacsPrefix') and
-- a quantifier-free CNF part ('qdimacsMatrix').
--
-- References:
--
-- * QDIMACS standard Ver. 1.1
--   <http://www.qbflib.org/qdimacs.html>
data QDimacs
  = QDimacs
  { qdimacsNumVars :: !Int
    -- ^ Number of variables
  , qdimacsNumClauses :: !Int
    -- ^ Number of clauses
  , qdimacsPrefix :: [QuantSet]
    -- ^ Sequence of quantifiers
  , qdimacsMatrix :: [SAT.PackedClause]
    -- ^ Clauses
  }
  deriving (Eq, Ord, Show, Read)

-- | Quantifier
data Quantifier
  = E -- ^ existential quantifier (∃)
  | A -- ^ universal quantifier (∀)
  deriving (Eq, Ord, Show, Read, Enum, Bounded)

-- | Quantified set of variables
type QuantSet = (Quantifier, [Atom])

-- | Synonym of 'SAT.Var'
type Atom = SAT.Var

instance FileFormat QDimacs where
  parse = f . BS.lines
    where
      f [] = Left "ToySolver.FileFormat.CNF.parse: premature end of file"
      f (l : ls) =
        case BS.uncons l of
          Nothing -> Left "ToySolver.FileFormat.CNF.parse: no problem line"
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
              _ -> Left "ToySolver.FileFormat.CNF.parse: invalid problem line"
          Just (c, _) -> Left ("ToySolver.FileFormat.CNF.parse: invalid prefix " ++ show c)

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
        _ -> error "ToySolver.FileFormat.CNF.parseProblem: invalid line"

-- -------------------------------------------------------------------
