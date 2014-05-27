-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Printer
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Printing utilities.
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Printer
  ( satPrintModel
  , maxsatPrintModel
  , pbPrintModel
  , musPrintSol
  ) where

import Control.Monad
import Data.Array.IArray
import Data.List
import System.IO
import ToySolver.SAT.Types

-- | Print a 'Model' in a way specified for SAT Competition.
-- See <http://www.satcompetition.org/2011/rules.pdf> for details.
satPrintModel :: Handle -> Model -> Int -> IO ()
satPrintModel h m n = do
  let as = if n > 0
           then takeWhile (\(v,_) -> v <= n) $ assocs m
           else assocs m
  forM_ (split 10 as) $ \xs -> do
    hPutStr h "v"
    forM_ xs $ \(var,val) -> hPutStr h (' ': show (literal var val))
    hPutStrLn h ""
  hPutStrLn h "v 0"
  hFlush h

-- | Print a 'Model' in a way specified for Max-SAT Evaluation.
-- See <http://maxsat.ia.udl.cat/requirements/> for details.
maxsatPrintModel :: Handle -> Model -> Int -> IO ()
maxsatPrintModel h m n = do
  let as = if n > 0
           then takeWhile (\(v,_) -> v <= n) $ assocs m
           else assocs m
  forM_ (split 10 as) $ \xs -> do
    hPutStr h "v"
    forM_ xs $ \(var,val) -> hPutStr h (' ' : show (literal var val))
    hPutStrLn h ""
  -- no terminating 0 is necessary
  hFlush stdout

-- | Print a 'Model' in a way specified for Pseudo-Boolean Competition.
-- See <http://www.cril.univ-artois.fr/PB12/format.pdf> for details.
pbPrintModel :: Handle -> Model -> Int -> IO ()
pbPrintModel h m n = do
  let as = if n > 0
           then takeWhile (\(v,_) -> v <= n) $ assocs m
           else assocs m
  forM_ (split 10 as) $ \xs -> do
    hPutStr h "v"
    forM_ xs $ \(var,val) -> hPutStr h (" " ++ (if val then "" else "-") ++ "x" ++ show var)
    hPutStrLn h ""
  hFlush stdout

musPrintSol :: Handle -> [Int] -> IO ()
musPrintSol h is = do
  forM_ (split 10 is) $ \xs -> do
    hPutStr h "v"
    forM_ xs $ \i -> hPutStr h (' ': show i)
    hPutStrLn h ""
  hPutStrLn h "v 0"
  hFlush h

-- ------------------------------------------------------------------------

split :: Int -> [a] -> [[a]]
split n = go
  where
    go [] = []
    go xs =
      case splitAt n xs of
        (ys, zs) -> ys : go zs
