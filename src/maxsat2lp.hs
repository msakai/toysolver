{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  maxsat2lp
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------

module Main where

import Data.List
import System.Environment
import System.Exit
import System.IO
import Text.Printf

type Lit = Int
type Clause = [Lit]
type Weight = Int
type WeightedClause = (Weight, Clause)

convert :: Int -> Weight -> [WeightedClause] -> String 
convert nvar top ls = unlines $
  [ "MINIMIZE" ] ++
  [ intercalate " + " [ printf "%d %s" w v | (v,(w,_)) <- zs, w < top ] ] ++
  [ "SUBJECT TO" ] ++
  [ case f xs of
      (s,n)
        | w==top    -> printf "%s >= %d" s (1 - n)       -- hard constraint
        | otherwise -> printf "%s+ %s >= %d" s z (1 - n) -- soft constraint
  | (z,(w,xs)) <- zs
  ] ++
  [ "BINARY" ] ++
  [ printf "x%d" n | n <- [(1::Int)..nvar]] ++ 
  [ z | (z,(w,_)) <- zs, w /= top ] ++
  [ "END" ]
  where
    zs = zip (map (\x -> "z" ++ show x) [(1::Int)..]) ls

    f :: [Lit] -> (String, Int)
    f = foldr phi ("",0)
      where
        phi lit (s,m)
         | lit >= 0  = (printf "+ x%d " lit ++ s, m)
         | otherwise = (printf "- x%d " (negate lit) ++ s, m+1)

isComment :: String -> Bool
isComment ('c':_) = True
isComment _ = False

parseWCNFLine :: String -> WeightedClause
parseWCNFLine s =
  case map read (words s) of
    (w:xs) -> (w, init xs)
    _ -> error "parse error"

parseCNFLine :: String -> WeightedClause
parseCNFLine s = (1, init (map read (words s)))

header :: String
header = "Usage: maxsat2lp [file.cnf|file.wcnf|-]"

main :: IO ()
main = do
  args <- getArgs
  s <- case args of
         ["-"]   -> getContents
         [fname] -> readFile fname
         _ -> hPutStrLn stderr header >> exitFailure
  let (l:ls) = filter (not . isComment) (lines s)
  case words l of
    (["p","wcnf", nvar, _, top]) -> do
      putStrLn $ convert (read nvar) (read top) (map parseWCNFLine ls)
    (["p","cnf", nvar, _]) -> do
      putStrLn $ convert (read nvar) 2 (map parseCNFLine ls)
    _ -> error "parse error"
