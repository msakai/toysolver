{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.LogParser
-- Copyright   :  (c) Masahiro Sakai 2025
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.SAT.LogParser
  ( parseSATLog
  , parseMaxSATLog
  , parsePBLog
  ) where

import Control.Monad
import Data.Array.IArray
import Data.Char

import ToySolver.SAT.Types as SAT

parseSATLog :: String -> SAT.Model
parseSATLog s = array (1, maximum (0 : map fst ys)) ys
  where
    xs = do
      l <- lines s
      case l of
        'v':l' -> map read (words l')
        _ -> mzero
    ys = [if y > 0 then (y, True) else (-y, False) | y <- takeWhile (0 /=) xs]

parseMaxSATLog :: String -> SAT.Model
parseMaxSATLog s =
  case f (lines s) Nothing [] of
    (_obj, vlines) ->
      let tmp = [c | c <- concat vlines, not (isSpace c)]
       in if all (\c -> c == '0' || c == '1') tmp then
            array (1, length tmp) [(v, c=='1') | (v, c) <- zip [1..] tmp]
          else
            let ys = [if l > 0 then (l, True) else (-l, False) | vline <- vlines, w <- words vline, let l = read w]
             in array (1, maximum (0 : map fst ys)) ys
  where
    f :: [String] -> Maybe Integer -> [String] -> (Maybe Integer, [String])
    f [] obj vlines = (obj, reverse vlines)
    f (l : ls) obj vlines =
      case l of
        'o':xs -> f ls (Just (read (dropWhile isSpace xs))) []
        'v':xs -> f ls obj (dropWhile isSpace xs : vlines)
        _ -> f ls obj vlines

parsePBLog :: String -> SAT.Model
parsePBLog s = array (1, maximum (0 : map fst ls2)) ls2
  where
    ls = lines s
    ls2 = do
      l <- ls
      case l of
        'v':xs -> do
          w <- words xs
          case w of
            '-':'x':ys -> return (read ys, False)
            'x':ys -> return (read ys, True)
            _ -> error "should not happen"
        _ -> mzero
