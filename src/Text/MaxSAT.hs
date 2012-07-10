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
-- TODO:
--
-- * Error handling
--
-----------------------------------------------------------------------------
module Text.MaxSAT
  (
    WCNF
  , WeightedClause
  , Weight

  -- * Parsing .cnf/.wcnf files
  , parseWCNFString
  , parseWCNFFile
  ) where

import qualified SAT.Types as SAT

type WCNF = (Int, Weight, [WeightedClause])

type WeightedClause = (Weight, SAT.Clause)

-- | should be able to represent 2^63
type Weight = Integer

parseWCNFString :: String -> WCNF
parseWCNFString s =
  case words l of
    (["p","wcnf", nvar, _nclause, top]) ->
      (read nvar, read top, map parseWCNFLine ls)
    (["p","wcnf", nvar, _nclause]) ->
      (read nvar, 2^(63::Int), map parseWCNFLine ls)
    (["p","cnf", nvar, _nclause]) ->
      (read nvar, 2, map parseCNFLine ls)
    _ -> error "parse error"
  where
    (l:ls) = filter (not . isComment) (lines s)

parseWCNFFile :: FilePath -> IO WCNF
parseWCNFFile filename = do
  s <- readFile filename
  return $! parseWCNFString s

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
