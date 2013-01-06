{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  lp2smt
-- Copyright   :  (c) Masahiro Sakai 2011-2012
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
import qualified Converter.LP2SMT as LP2SMT

data Flag
    = Help
    | Optimize
    | NoCheck
    | NoProduceModel
    | Yices
    deriving Eq

options :: [OptDescr Flag]
options =
    [ Option ['h'] ["help"]  (NoArg Help)       "show help"
    , Option [] ["yices"]    (NoArg Yices)      "output .ys instead of .smt2"
    , Option [] ["optimize"] (NoArg Optimize)   "output optimiality condition which uses quantifiers"
    , Option [] ["no-check"] (NoArg NoCheck)    "do not output \"(check)\""
    , Option [] ["no-produce-model"] (NoArg NoProduceModel) "do not output \"(set-option :produce-models true)\""
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
        Right lp -> do
          let opt = LP2SMT.defaultOptions
                    { LP2SMT.optLanguage     = if Yices `elem` o then LP2SMT.YICES else LP2SMT.SMTLIB2
                    , LP2SMT.optCheckSAT     = not (NoCheck `elem` o)
                    , LP2SMT.optProduceModel = not (NoProduceModel `elem` o)
                    , LP2SMT.optOptimize     = Optimize `elem` o
                    }
          putStrLn $ LP2SMT.convert opt lp ""
        Left err -> hPrint stderr err >> exitFailure
    (_,_,errs) -> do
        hPutStrLn stderr $ concat errs ++ usageInfo header options
        exitFailure

header :: String
header = "Usage: lp2smt [OPTION]... [file.lp|-]"
