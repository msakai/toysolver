{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  pb2lp
-- Copyright   :  (c) Masahiro Sakai 2011-2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Main where

import Control.Monad
import Data.Char
import System.Environment
import System.IO
import System.Exit
import System.Console.GetOpt
import qualified Text.PBFile as PBFile
import qualified Text.LPFile as LPFile
import Converter.PB2LP

data Flag
  = Help
  | WBO
  | ObjType ObjType
  | IndicatorConstraint
  deriving Eq

options :: [OptDescr Flag]
options =
    [ Option ['h'] ["help"] (NoArg Help) "show help"
    , Option []    ["wbo"]  (NoArg WBO)  "input is .wbo file"
    , Option []    ["obj"]  (ReqArg (ObjType . parseObjType) "STRING") "objective function for PBS: none (default), max-one, max-zero"
    , Option []    ["indicator"] (NoArg IndicatorConstraint) "use indicator constraints in output LP file"
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
      let objType = last (ObjNone : [t | ObjType t <- o])
      lp <-
        if WBO `elem` o
        then do
          ret <- if fname == "-"
                 then liftM (PBFile.parseWBOString "-") getContents
                 else PBFile.parseWBOFile fname
          case ret of
            Left err -> hPrint stderr err >> exitFailure
            Right formula -> return (convertWBO formula (IndicatorConstraint `elem` o))
        else do
          ret <- if fname == "-"
                 then liftM (PBFile.parseOPBString "-") getContents
                 else PBFile.parseOPBFile fname
          case ret of
            Left err -> hPrint stderr err >> exitFailure
            Right formula -> return (convert objType formula)
      case LPFile.render lp of
        Nothing -> hPutStrLn stderr "conversion failure" >> exitFailure
        Just s -> putStr s
    (_,_,errs) ->
      hPutStrLn stderr $ concat errs ++ usageInfo header options

header :: String
header = "Usage: pb2lp [--wbo] [file.opb|file.wbo|-]"
