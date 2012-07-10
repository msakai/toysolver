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
import qualified Data.Map as Map
import System.Environment
import System.Exit
import System.IO
import Text.Printf
import Text.MaxSAT
import SAT.Types

convert :: WCNF -> String 
convert (nvar, top, ls) = unlines $
  [ "MINIMIZE" ] ++
  [ printf "+ %d %s" w v | (v,(w,_)) <- zs, w < top ] ++
  [ "SUBJECT TO" ] ++
  [ case f xs of
      (s,n)
        | w>=top    -> printf "%s >= %d" (g s) (1 - n)        -- hard constraint
        | otherwise -> printf "%s + %s >= %d" (g s) z (1 - n) -- soft constraint
  | (z,(w,xs)) <- zs
  ] ++
  [ "BINARY" ] ++
  [ printf "x%d" n | n <- [(1::Int)..nvar]] ++ 
  [ z | (z,(w,_)) <- zs, w /= top ] ++
  [ "END" ]
  where
    zs = zip (map (\x -> "z" ++ show x) [(1::Int)..]) ls

    f :: [Lit] -> (Map.Map Var Int, Int)
    f = foldr phi (Map.empty,0)
      where        
        phi lit (s,m)
         | lit >= 0  = (Map.insertWith (+) (abs lit) 1 s, m)
         | otherwise = (Map.insertWith (+) (abs lit) (-1) s, m+1)

    g :: Map.Map Var Int -> String
    g m = intercalate " " $ do
      (v,c) <- Map.toList m
      let sign = if c < 0 then "-" else "+"
      let c' = abs c
      return $
        if c' == 1
        then printf "%s x%d" sign v
        else printf "%s %d x%d" sign c' v

header :: String
header = "Usage: maxsat2lp [file.cnf|file.wcnf|-]"

main :: IO ()
main = do
  args <- getArgs
  s <- case args of
         ["-"]   -> getContents
         [fname] -> readFile fname
         _ -> hPutStrLn stderr header >> exitFailure
  let wcnf = parseWCNFString s
  putStrLn $ convert wcnf
