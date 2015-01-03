{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
module Main where

import Control.Monad
import Data.List
import qualified Data.IntSet as IntSet
import System.Environment
import qualified ToySolver.HittingSet.Simple as HittingSet

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fname] -> do
      s <- readFile fname
      let xss = filter (not . IntSet.null) . fmap (IntSet.fromList . fmap read . words) . lines $ s
      forM_ (HittingSet.minimalHittingSets xss) $ \ys -> do
        putStrLn $ intercalate " " $ map show $ IntSet.toList ys
