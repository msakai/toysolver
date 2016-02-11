{-# LANGUAGE ScopedTypeVariables, CPP #-}
{-# OPTIONS_GHC -Wall #-}
module Main where

import Control.Monad
import Data.Char
import Data.List
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import System.Environment
import System.Exit
import System.IO
import qualified ToySolver.Combinatorial.HittingSet.Simple as HittingSet
import qualified ToySolver.Combinatorial.HittingSet.GurvichKhachiyan1999 as GurvichKhachiyan1999
import ToySolver.Internal.Util (setEncodingChar8)

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif

  args <- getArgs
  case args of
    [] -> do
      hPutStrLn stderr "USAGE: htc [METHOD] FILENAME"
      hPutStrLn stderr ""
      hPutStrLn stderr "Supported METHODs:"
      hPutStrLn stderr "  simple"
      hPutStrLn stderr "  gurvichkhachiyan1999"
    [method, fname] -> f (Just method) fname
    [fname] -> f Nothing fname

f :: Maybe String -> FilePath -> IO ()
f method fname = do
  s <- readFile fname
  let xss = Set.fromList . filter (not . IntSet.null) . fmap (IntSet.fromList . fmap read . words) . lines $ s
  yss <-
    case method of
      Nothing -> return $ HittingSet.minimalHittingSets xss
      Just s ->
        case filter (not . (`elem` ['-', '_'])) (map toLower s) of
          "simple" -> return $ HittingSet.minimalHittingSets xss
          "gurvichkhachiyan1999" -> return $ GurvichKhachiyan1999.minimalHittingSets xss
          "gurvichkhachiyan" -> return $ GurvichKhachiyan1999.minimalHittingSets xss
          _ -> do
            hPutStrLn stderr ("unknown method: " ++ s)
            exitFailure
  forM_ (Set.toList yss) $ \ys -> do
    putStrLn $ intercalate " " $ map show $ IntSet.toList ys
