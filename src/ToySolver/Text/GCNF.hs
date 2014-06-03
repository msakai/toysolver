{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.GCNF
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
-- 
-- References:
-- 
-- * <http://www.satcompetition.org/2011/rules.pdf>
--
--
-----------------------------------------------------------------------------
module ToySolver.Text.GCNF
  (
    GCNF (..)
  , GroupIndex
  , GClause

  -- * Parsing .gcnf files
  , parseString
  , parseFile
  ) where

import qualified ToySolver.SAT.Types as SAT
import ToySolver.Internal.TextUtil

data GCNF
  = GCNF
  { numVars        :: !Int
  , numClauses     :: !Int
  , lastGroupIndex :: !GroupIndex
  , clauses        :: [GClause]
  }

type GroupIndex = Int

type GClause = (GroupIndex, SAT.Clause)

parseString :: String -> Either String GCNF
parseString s =
  case words l of
    (["p","gcnf", nbvar', nbclauses', lastGroupIndex']) ->
      Right $
        GCNF
        { numVars        = read nbvar'
        , numClauses     = read nbclauses'
        , lastGroupIndex = read lastGroupIndex'
        , clauses        = map parseLine ls
        }
    (["p","cnf", nbvar', nbclause']) ->
      Right $
        GCNF
        { numVars        = read nbvar'
        , numClauses     = read nbclause'
        , lastGroupIndex = read nbclause'
        , clauses        = zip [1..] $ map parseCNFLine ls
        }
    _ ->
      Left "cannot find gcnf header"
  where
    (l:ls) = filter (not . isComment) (lines s)

parseFile :: FilePath -> IO (Either String GCNF)
parseFile filename = do
  s <- readFile filename
  return $ parseString s

isComment :: String -> Bool
isComment ('c':_) = True
isComment _ = False

parseLine :: String -> GClause
parseLine s =
  case words s of
    (('{':w):xs) ->
        let ys  = map readInt $ init xs
            idx = readInt $ init w
        in seq idx $ seqList ys $ (idx, ys)
    _ -> error "ToySolver.Text.GCNF: parse error"

parseCNFLine :: String -> SAT.Clause
parseCNFLine s = seq xs $ seqList xs $ xs
  where
    xs = init (map readInt (words s))

seqList :: [a] -> b -> b
seqList [] b = b
seqList (x:xs) b = seq x $ seqList xs b
