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
  , parseWCNFString
  , parseWCNFFile
  ) where

import qualified SAT.Types as SAT

data WCNF
  = WCNF
  { numVars    :: !Int
  , numClauses :: !Int
  , topCost    :: !Weight
  , clauses    :: [WeightedClause]
  }

type WeightedClause = (Weight, SAT.Clause)

-- | should be able to represent 2^63
type Weight = Integer

parseWCNFString :: String -> Either String WCNF
parseWCNFString s =
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
        , topCost    = 2^(63::Int)
        , clauses    = map parseWCNFLine ls
        }
    (["p","cnf", nvar, nclause]) ->
      Right $
        WCNF
        { numVars    = read nvar
        , numClauses = read nclause
        , topCost    = 2
        , clauses    = map parseCNFLine ls
        }
    _ ->
      Left "cannot find wcnf/cnf header"
  where
    (l:ls) = filter (not . isComment) (lines s)

parseWCNFFile :: FilePath -> IO (Either String WCNF)
parseWCNFFile filename = do
  s <- readFile filename
  return $ parseWCNFString s

isComment :: String -> Bool
isComment ('c':_) = True
isComment _ = False

parseWCNFLine :: String -> WeightedClause
parseWCNFLine s =
  case map read (words s) of
    (w:xs) ->
        let ys = map fromIntegral $ init xs
        in seq w $ seqList ys $ (w, ys)
    _ -> error "parse error"

parseCNFLine :: String -> WeightedClause
parseCNFLine s = seq xs $ seqList xs $ (1, xs)
  where
    xs = init (map read (words s))

seqList :: [a] -> b -> b
seqList [] b = b
seqList (x:xs) b = seq x $ seqList xs b
