{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
module Main where

import Control.Monad
import Data.List
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import System.Environment
import qualified ToySolver.Combinatorial.HittingSet.Simple as HittingSet

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fname] -> do
      s <- readFile fname
      let xss = Set.fromList . filter (not . IntSet.null) . fmap (IntSet.fromList . fmap read . words) . lines $ s
      forM_ (Set.toList (HittingSet.minimalHittingSets xss)) $ \ys -> do
        putStrLn $ intercalate " " $ map show $ IntSet.toList ys
