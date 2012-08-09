{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  cnf2lp
-- Copyright   :  (c) Masahiro Sakai 2011-2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Main where

import qualified Data.ByteString.Lazy as BS
import Data.Char
import System.IO
import System.Environment
import System.Exit
import System.Console.GetOpt

import qualified Text.LPFile as LPFile
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS

import Converter.CNF2LP

data Flag
  = Help
  | ObjType ObjType
  deriving Eq

options :: [OptDescr Flag]
options =
    [ Option ['h'] ["help"] (NoArg Help)                       "show help"
    , Option []    ["obj"]  (ReqArg (ObjType . parseObjType) "STRING") "none (default), max-one, max-zero"
    ]
  where
    parseObjType s =
      case map toLower s of
        "none"     -> ObjNone
        "max-one"  -> ObjMaxOne
        "max-zero" -> ObjMaxZero
        _          -> error ("unknown obj: " ++ s)

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (o,_,[])
      | Help `elem` o -> putStrLn (usageInfo header options)
    (o,[fname],[]) -> do
      ret <- case fname of
               "-" -> fmap (DIMACS.parseByteString "-") $ BS.hGetContents stdin
               _   -> DIMACS.parseFile fname
      case ret of
        Left err -> hPrint stderr err >> exitFailure
        Right cnf -> do
          let objType = last (ObjNone : [t | ObjType t <- o])
          case LPFile.render (convert objType cnf) of
            Nothing -> hPutStrLn stderr "conversion failure" >> exitFailure
            Just s2 -> putStr s2
    (_,_,errs) -> do
      hPutStrLn stderr $ concat errs ++ usageInfo header options
      exitFailure

header :: String
header = "Usage: cnf2lp [OPTION]... [file.cnf|-]"
