{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Text.MaxSAT
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
module Text.MaxSAT
  (
    WCNF (..)
  , WeightedClause
  , Weight

  -- * Parsing .cnf/.wcnf files
  , parseFile
  , parseString
  , parseByteString
  ) where

import qualified Data.ByteString.Lazy.Char8 as BS
import Data.Char
import qualified SAT.Types as SAT
import ToySolver.Internal.TextUtil

data WCNF
  = WCNF
  { numVars    :: !Int
  , numClauses :: !Int
  , topCost    :: !Weight
  , clauses    :: [WeightedClause]
  }

type WeightedClause = (Weight, SAT.Clause)

-- | Weigths must be greater than or equal to 1, and smaller than 2^63.
type Weight = Integer

parseFile :: FilePath -> IO (Either String WCNF)
parseFile filename = do
{-
  s <- readFile filename
  return $ parseString s
-}
  s <- BS.readFile filename
  return $ parseByteString s

parseString :: String -> Either String WCNF
parseString s =
  case words l of
    (["p","wcnf", nvar, nclause, top]) ->
      Right $
        WCNF
        { numVars    = read nvar
        , numClauses = read nclause
        , topCost    = read top
        , clauses    = map parseWCNFLine ls
        }
    (["p","wcnf", nvar, nclause]) ->
      Right $
        WCNF
        { numVars    = read nvar
        , numClauses = read nclause
          -- top must be greater than the sum of the weights of violated soft clauses.
        , topCost    = fromInteger $ 2^(63::Int) - 1
        , clauses    = map parseWCNFLine ls
        }
    (["p","cnf", nvar, nclause]) ->
      Right $
        WCNF
        { numVars    = read nvar
        , numClauses = read nclause
          -- top must be greater than the sum of the weights of violated soft clauses.
        , topCost    = fromInteger $ 2^(63::Int) - 1
        , clauses    = map parseCNFLine ls
        }
    _ ->
      Left "cannot find wcnf/cnf header"
  where
    (l:ls) = filter (not . isComment) (lines s)

isComment :: String -> Bool
isComment ('c':_) = True
isComment _ = False

parseWCNFLine :: String -> WeightedClause
parseWCNFLine s =
  case words s of
    (w:xs)
      | last xs == "0" -> seq w' $ seqList ys $ (w', ys)
      | otherwise -> error "parse error"
      where
        w' = readUnsignedInteger w
        ys = map readInt $ init xs
    _ -> error "parse error"

parseCNFLine :: String -> WeightedClause
parseCNFLine s
  | null xs || last xs /= 0 = error "parse error"
  | otherwise = seqList ys $ (1, ys)
  where
    xs = map readInt (words s)
    ys = init xs

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
    Nothing -> error "no weight"
    Just (w, s') -> seq w $ seq xs $ (w, xs)
      where
        xs = parseClauseBS s'

parseCNFLineBS :: BS.ByteString -> WeightedClause
parseCNFLineBS s = seq xs $ (1, xs)
  where
    xs = parseClauseBS s

parseClauseBS :: BS.ByteString -> SAT.Clause
parseClauseBS s = seqList xs $ xs
  where
    xs = go s
    go s =
      case BS.readInt (BS.dropWhile isSpace s) of
        Nothing -> error "parse error"
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
