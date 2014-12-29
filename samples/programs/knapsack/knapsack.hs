{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
module Main where

import Control.Monad
import Data.List
import System.Environment
import System.IO
import Text.Printf
import qualified ToySolver.Knapsack.BB as Knapsack

type Value = Integer
type Weight = Integer

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fname] -> do
      (items, capa) <- load fname
      let (val,_w,sol) = Knapsack.solve [(fromInteger val, fromInteger weight) | (val, weight) <- items] (fromInteger capa)
      printf "%d %d\n" (round val :: Integer) (1::Int)
      putStrLn $ intersperse ' ' [if b then '1' else '0' | b <- sol]

load :: FilePath -> IO ([(Value, Weight)], Weight)
load fname =
  withFile fname ReadMode $ \h -> do
    [nitems, capa] <- liftM (map read . words) $ hGetLine h
    items <- replicateM (fromInteger nitems) $ do
      [value,weight] <- liftM (map read . words) $ hGetLine h
      return (value, weight)
    return (items, capa)
