{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  lp2yices
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Main where

import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
import qualified Text.LPFile as LP
import qualified Converter.LP2Yices as LP2Yices

data Flag
    = Help
    | Optimize
    | NoCheck
    deriving Eq

options :: [OptDescr Flag]
options =
    [ Option ['h'] ["help"]  (NoArg Help)       "show help"
    , Option [] ["optimize"] (NoArg Optimize)   "output optimiality condition which uses quantifiers"
    , Option [] ["no-check"] (NoArg NoCheck)    "do not output \"(check)\""
    ]

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (o,_,[])
      | Help `elem` o    -> putStrLn (usageInfo header options)
    (o,[fname],[]) -> do
      ret <- if fname == "-"
             then fmap (LP.parseString "-") getContents
             else LP.parseFile fname
      case ret of
        Right lp -> putStrLn $ LP2Yices.convert lp (Optimize `elem` o) (not (NoCheck `elem` o)) ""
        Left err -> hPrint stderr err >> exitFailure
    (_,_,errs) -> do
        hPutStrLn stderr $ concat errs ++ usageInfo header options
        exitFailure

header :: String
header = "Usage: lp2yice [OPTION]... [file.lp|-]"
