{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
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

import Data.Array.IArray
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.Char
import Data.Maybe (fromMaybe)
import qualified Data.Vector.Unboxed as VU

import ToySolver.SAT.Types as SAT

parseSATLog :: BL.ByteString -> (BS.ByteString, Maybe SAT.Model)
parseSATLog s = f "UNKNOWN" Nothing (BL.lines s)
  where
    f :: BS.ByteString -> Maybe [BL.ByteString] -> [BL.ByteString] -> (BS.ByteString, Maybe SAT.Model)
    f !status vlines (l : ls) =
      case BL.uncons l of
        Just ('c', _) -> f status vlines ls
        Just ('s', BS.toStrict -> BS.strip -> rest) -> f rest vlines ls
        Just ('v', rest) ->
          let vlines' = Just $ rest : fromMaybe [] vlines
           in f status vlines' ls
        Just (c, _) -> error ("unknown line type: " ++ show c)
        Nothing -> f status vlines ls
    f !status vlines [] =
      ( status
      , case vlines of
          Nothing -> Nothing
          Just lss ->
            let xs = VU.fromList $ map (read . BL.unpack) $ concat $ map BL.words $ reverse lss
                xs' = VU.init xs
                n = maximum $ map abs $ VU.toList xs'
             in if VU.last xs /= 0 then
                  error "vlines are not terminated with zero"
                else if 0 `VU.elem` xs' then
                  error "multiple zeros in vlines"
                else
                  Just $ array (1, n) [if lit > 0 then (lit, True) else (- lit, False) | lit <- VU.toList xs']
      )

parseMaxSATLog :: BL.ByteString -> (BS.ByteString, Maybe Integer, Maybe SAT.Model)
parseMaxSATLog s = f "UNKNOWN" Nothing Nothing (BL.lines s)
  where
    f :: BS.ByteString -> Maybe Integer -> Maybe [BL.ByteString] -> [BL.ByteString] -> (BS.ByteString, Maybe Integer, Maybe SAT.Model)
    f !status obj vlines (l : ls) =
      case BL.uncons l of
        Just ('c', _) -> f status obj vlines ls
        Just ('s', BL.toStrict -> BS.strip -> rest) -> f rest obj vlines ls
        Just ('v', rest) ->
          let vlines' = Just $ rest : fromMaybe [] vlines
           in f status obj vlines' ls
        Just ('o', BL.toStrict -> BS.strip -> rest) ->
          case BS.readInteger rest of
            Just (!val, "") -> f status (Just val) Nothing ls
            _ -> error "failed to parse o-line"
        Just (c, _) -> error ("unknown line type: " ++ show c)
        Nothing -> f status obj vlines ls
    f !status obj vlines [] =
      ( status
      , obj
      , case vlines of
          Nothing -> Nothing
          Just lss ->
            let tmp1 = BL.filter (not . isSpace) $ BL.concat $ reverse lss
                tmp2 = map (read . BL.unpack) $ concat $ map BL.words $ reverse lss
             in if BL.all (\c -> c == '0' || c == '1') tmp1 then
                  Just $ array (1, fromIntegral (BL.length tmp1)) [(v, c=='1') | (v, c) <- zip [1..] (BL.unpack tmp1)]
                else
                  Just $ array (1, maximum (map abs tmp2)) [if lit > 0 then (lit, True) else (- lit, False) | lit <- tmp2]
      )

parsePBLog :: BL.ByteString -> (BS.ByteString, Maybe Integer, Maybe SAT.Model)
parsePBLog s = f "UNKNOWN" Nothing Nothing (BL.lines s)
  where
    f :: BS.ByteString -> Maybe Integer -> Maybe [BL.ByteString] -> [BL.ByteString] -> (BS.ByteString, Maybe Integer, Maybe SAT.Model)
    f !status obj vlines (l : ls) =
      case BL.uncons l of
        Just ('c', _) -> f status obj vlines ls
        Just ('s', BL.toStrict -> BS.strip -> rest) -> f rest obj vlines ls
        Just ('v', rest) ->
          let vlines' = Just $ rest : fromMaybe [] vlines
           in f status obj vlines' ls
        Just ('o', BL.toStrict -> BS.strip -> rest) ->
          case BS.readInteger rest of
            Just (!val, "") -> f status (Just val) Nothing ls
            _ -> error "failed to parse o-line"
        Just (c, _) -> error ("unknown line type: " ++ show c)
        Nothing -> f status obj vlines ls
    f !status obj vlines [] =
      ( status
      , obj
      , case vlines of
          Nothing -> Nothing
          Just lss ->
            let lits = map (parseLit . BL.unpack) $ concat $ map BL.words $ reverse lss
             in Just $ array (1, maximum (map abs lits)) [if lit > 0 then (lit, True) else (- lit, False) | lit <- lits]
      )

    parseLit :: String -> SAT.Lit
    parseLit ('-' : 'x' : rest) | [(v, "")] <- reads rest = - v
    parseLit ('x' : rest) | [(v, "")] <- reads rest = v
    parseLit w = error ("failed to parse a literal: " ++ show w)
