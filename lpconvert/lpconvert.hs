{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  lpconvert
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------

module Main where

import Data.Char
import qualified Data.Version as V
import System.Environment
import System.IO
import System.Exit
import System.FilePath
import System.Console.GetOpt
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS

import qualified Text.LPFile as LPFile
import qualified Text.MaxSAT as MaxSAT
import qualified Text.MPSFile as MPSFile
import qualified Text.PBFile as PBFile
import Converter.ObjType
import qualified Converter.SAT2LP as SAT2LP
import qualified Converter.LP2SMT as LP2SMT
import qualified Converter.MaxSAT2LP as MaxSAT2LP
import qualified Converter.PB2LP as PB2LP
import Version

data Flag
  = Help
  | Version
  | Output String
  | AsMaxSAT
  | ObjType ObjType
  | IndicatorConstraint
  | Optimize
  | NoCheck
  | NoProduceModel
  deriving Eq

options :: [OptDescr Flag]
options =
    [ Option ['h'] ["help"] (NoArg Help) "show help"
    , Option ['v'] ["version"] (NoArg Version)         "show version number"
    , Option ['o'] [] (ReqArg Output "FILE") "output filename"
    , Option []    ["max-sat"]  (NoArg AsMaxSAT)  "treat *.cnf file as MAX-SAT problem"
    , Option []    ["obj"] (ReqArg (ObjType . parseObjType) "STRING") "objective function for SAT/PBS: none (default), max-one, max-zero"
    , Option []    ["indicator"] (NoArg IndicatorConstraint) "use indicator constraints in output LP file"
    , Option []    ["smt-optimize"] (NoArg Optimize)   "output optimiality condition which uses quantifiers"
    , Option []    ["smt-no-check"] (NoArg NoCheck)    "do not output \"(check)\""
    , Option []    ["smt-no-produce-model"] (NoArg NoProduceModel) "do not output \"(set-option :produce-models true)\""    
    ]
  where
    parseObjType s =
      case map toLower s of
        "none"     -> ObjNone
        "max-one"  -> ObjMaxOne
        "max-zero" -> ObjMaxZero
        _          -> error ("unknown obj: " ++ s)

header :: String
header = unlines
  [ "Usage:"
  , "    lpconvert -o <outputfile> <inputfile>"
  , ""
  , "Supported formats:"
  , "    input: .lp .mps .cnf .wcnf .opb .wbo"
  , "    output: .lp .smt2 .ys"
  , ""
  , "Options:"
  ]

readLP :: [Flag] -> String -> IO LPFile.LP
readLP o fname = do
  let objType = last (ObjNone : [t | ObjType t <- o])
  case map toLower (takeExtension fname) of
    ".cnf"
      | AsMaxSAT `elem` o -> readWCNF
      | otherwise -> do
          ret <- DIMACS.parseFile fname
          case ret of
            Left err -> hPrint stderr err >> exitFailure
            Right cnf -> do
              let (lp, _) = SAT2LP.convert objType cnf
              return lp
    ".wcnf" -> readWCNF
    ".opb"  -> do
      ret <- PBFile.parseOPBFile fname
      case ret of
        Left err -> hPrint stderr err >> exitFailure
        Right formula -> do
          let (lp, _) = PB2LP.convert objType formula
          return lp
    ".wbo"  -> do
      ret <- PBFile.parseWBOFile fname
      case ret of
        Left err -> hPrint stderr err >> exitFailure
        Right formula -> do
          let (lp, _) = PB2LP.convertWBO (IndicatorConstraint `elem` o) formula
          return lp
    ".lp"   -> do
      ret <- LPFile.parseFile fname
      case ret of
        Left err -> hPrint stderr err >> exitFailure
        Right lp -> return lp
    ".mps"  -> do
      ret <- MPSFile.parseFile fname
      case ret of
        Left err -> hPrint stderr err >> exitFailure
        Right lp -> return lp
    ext ->
      error $ "unknown file extension: " ++ show ext
  where
    readWCNF = do
      ret <- MaxSAT.parseWCNFFile fname
      case ret of
        Left err -> hPutStrLn stderr err >> exitFailure
        Right wcnf -> do
          let (lp, _) = MaxSAT2LP.convert (IndicatorConstraint `elem` o) wcnf
          return lp

writeLP :: [Flag] -> LPFile.LP -> IO ()
writeLP o lp = do
  let lp2smtOpt =
        LP2SMT.defaultOptions
        { LP2SMT.optCheckSAT     = not (NoCheck `elem` o)
        , LP2SMT.optProduceModel = not (NoProduceModel `elem` o)
        , LP2SMT.optOptimize     = Optimize `elem` o
        }

  case head ([Just fname | Output fname <- o] ++ [Nothing]) of
    Nothing -> do
      case LPFile.render lp of
        Nothing -> hPutStrLn stderr "conversion failure" >> exitFailure
        Just s -> putStr s
    Just fname -> do
      case map toLower (takeExtension fname) of
        ".lp" -> do
          case LPFile.render lp of
            Nothing -> hPutStrLn stderr "conversion failure" >> exitFailure
            Just s -> writeFile fname s
        ".smt2" -> do
          writeFile fname (LP2SMT.convert lp2smtOpt lp "")
        ".ys" -> do
          writeFile fname (LP2SMT.convert lp2smtOpt{ LP2SMT.optLanguage = LP2SMT.YICES } lp "")
        ext -> do
          error $ "unknown file extension: " ++ show ext
          
main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (o,_,[])
      | Help `elem` o    -> putStrLn (usageInfo header options)
      | Version `elem` o -> putStrLn (V.showVersion version)
    (o,[fname],[]) -> do
      lp <- readLP o fname
      writeLP o lp
    (_,_,errs) -> do
      hPutStrLn stderr $ concat errs ++ usageInfo header options
      exitFailure
