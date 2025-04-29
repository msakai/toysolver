{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Printer
-- Copyright   :  (c) Masahiro Sakai 2012-2025
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Printing utilities.
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Printer
  (
  -- * Model/Solution printer
    satPrintModel
  , maxsatPrintModel
  , maxsatPrintModelCompact
  , pbPrintModel
  , musPrintSol

  -- * Low-level builder functions
  , satModel
  , maxsatModel
  , maxsatModelCompact
  , pbModel
  , musSol
  ) where

import Data.Array.IArray
import qualified Data.ByteString.Builder as Builder
import System.IO
import ToySolver.SAT.Types

-- | Print a 'Model' in a way specified for SAT Competition.
-- See <http://www.satcompetition.org/2011/rules.pdf> for details.
satPrintModel :: Handle -> Model -> Int -> IO ()
satPrintModel h m n = do
  newline <- getNewline h
  Builder.hPutBuilder h $ satModel m n newline
  hFlush h

-- | Print a 'Model' in a way specified for Max-SAT Evaluation.
-- See <http://maxsat.ia.udl.cat/requirements/> for details.
maxsatPrintModel :: Handle -> Model -> Int -> IO ()
maxsatPrintModel h m n = do
  newline <- getNewline h
  Builder.hPutBuilder h $ maxsatModel m n newline
  hFlush h

-- | Print a 'Model' in the new compact way specified for Max-SAT Evaluation >=2020.
-- See <https://maxsat-evaluations.github.io/2020/vline.html> for details.
maxsatPrintModelCompact :: Handle -> Model -> Int -> IO ()
maxsatPrintModelCompact h m n = do
  newline <- getNewline h
  Builder.hPutBuilder h $ maxsatModelCompact m n newline
  hFlush h

-- | Print a 'Model' in a way specified for Pseudo-Boolean Competition.
-- See <http://www.cril.univ-artois.fr/PB12/format.pdf> for details.
pbPrintModel :: Handle -> Model -> Int -> IO ()
pbPrintModel h m n = do
  newline <- getNewline h
  Builder.hPutBuilder h $ pbModel m n newline
  hFlush h

musPrintSol :: Handle -> [Int] -> IO ()
musPrintSol h is = do
  newline <- getNewline h
  Builder.hPutBuilder h $ musSol is newline
  hFlush h

-- ------------------------------------------------------------------------

satModel :: Model -> Int -> Newline -> Builder.Builder
satModel m n newline = mconcat
  [ Builder.char7 'v' <> mconcat [Builder.char7 ' ' <> Builder.intDec (literal var val) | (var, val) <- xs] <> nl
  | xs <- split 10 as
  ] <> Builder.string7 "v 0" <> nl
  where
    as = if n > 0
         then takeWhile (\(v,_) -> v <= n) $ assocs m
         else assocs m
    nl = newlineBuilder newline

maxsatModel :: Model -> Int -> Newline -> Builder.Builder
maxsatModel m n newline = mconcat
  [ Builder.char7 'v' <> mconcat [Builder.char7 ' ' <> Builder.intDec (literal var val) | (var, val) <- xs] <> nl
  | xs <- split 10 as
  ] -- no terminating 0 is necessary
  where
    as = if n > 0
         then takeWhile (\(v,_) -> v <= n) $ assocs m
         else assocs m
    nl = newlineBuilder newline

maxsatModelCompact :: Model -> Int -> Newline -> Builder.Builder
maxsatModelCompact m n newline =
  Builder.string7 "v " <> mconcat [Builder.char7 (if v then '1' else '0') | v <- vs] <> nl
  where
    vs = if n > 0
         then take n $ elems m
         else elems m
    nl = newlineBuilder newline

pbModel :: Model -> Int -> Newline -> Builder.Builder
pbModel m n newline = mconcat
  [ Builder.char7 'v' <> mconcat
    [ Builder.char7 ' ' <> (if val then mempty else Builder.char7 '-') <> Builder.char7 'x' <> Builder.intDec var
    | (var, val) <- xs
    ] <> nl
  | xs <- split 10 as
  ]
  where
    as = if n > 0
         then takeWhile (\(v,_) -> v <= n) $ assocs m
         else assocs m
    nl = newlineBuilder newline

musSol :: [Int] -> Newline -> Builder.Builder
musSol is newline = mconcat
  [ Builder.char7 'v' <> mconcat [Builder.char7 ' ' <> Builder.intDec i | i <- xs] <> nl
  | xs <- split 10 is
  ] <> Builder.string7 "v 0" <> nl
  where
    nl = newlineBuilder newline

-- ------------------------------------------------------------------------

split :: Int -> [a] -> [[a]]
split n = go
  where
    go [] = []
    go xs =
      case splitAt n xs of
        (ys, zs) -> ys : go zs

#ifdef mingw32_HOST_OS

getNewline :: Handle -> IO Newline
getNewline h = do
  m <- hGetEncoding h
  case m of
    Nothing -> return LF
    Just _ -> return CRLF

#else

getNewline :: Handle -> IO Newline
getNewline _ = return LF

#endif

newlineBuilder :: Newline -> Builder.Builder
newlineBuilder LF = Builder.char7 '\n'
newlineBuilder CRLF = Builder.string7 "\r\n"
