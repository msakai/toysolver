{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  pbconvert
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
import qualified Text.PBFile as PBFile
import Converter.ObjType
import qualified Converter.SAT2PB as SAT2PB
import qualified Converter.LP2SMT as LP2SMT
import qualified Converter.MaxSAT2WBO as MaxSAT2WBO
import qualified Converter.MaxSAT2NLPB as MaxSAT2NLPB
import qualified Converter.PB2LP as PB2LP
import qualified Converter.PB2LSP as PB2LSP
import qualified Converter.PB2WBO as PB2WBO
import qualified Converter.WBO2PB as WBO2PB
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
  | MaxSATNonLinear
  deriving Eq

options :: [OptDescr Flag]
options =
    [ Option ['h'] ["help"] (NoArg Help) "show help"
    , Option ['v'] ["version"] (NoArg Version)         "show version number"
    , Option ['o'] [] (ReqArg Output "FILE") "output filename"
    , Option []    ["maxsat"]  (NoArg AsMaxSAT)  "treat *.cnf file as MAX-SAT problem"
    , Option []    ["obj"] (ReqArg (ObjType . parseObjType) "STRING") "objective function for SAT/PBS: none (default), max-one, max-zero"
    , Option []    ["indicator"] (NoArg IndicatorConstraint) "use indicator constraints in output LP file"
    , Option []    ["smt-optimize"] (NoArg Optimize)   "output optimiality condition which uses quantifiers"
    , Option []    ["smt-no-check"] (NoArg NoCheck)    "do not output \"(check)\""
    , Option []    ["smt-no-produce-model"] (NoArg NoProduceModel) "do not output \"(set-option :produce-models true)\""    
    , Option []    ["maxsat-nonlinear"] (NoArg MaxSATNonLinear) "use non-linear formulation of Max-SAT"
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
  , "    pbconvert -o <outputfile> <inputfile>"
  , ""
  , "Supported formats:"
  , "    input: .cnf .wcnf .opb .wbo"
  , "    output: .opb .wbo"
  , ""
  , "Options:"
  ]

readPBFile :: [Flag] -> String -> IO (Either PBFile.Formula PBFile.SoftFormula)
readPBFile o fname = do
  case map toLower (takeExtension fname) of
    ".cnf"
      | AsMaxSAT `elem` o -> readWCNF
      | otherwise -> do
          ret <- DIMACS.parseFile fname
          case ret of
            Left err  -> hPrint stderr err >> exitFailure
            Right cnf -> return $ Left $ SAT2PB.convert cnf
    ".wcnf" -> readWCNF
    ".opb"  -> do
      ret <- PBFile.parseOPBFile fname
      case ret of
        Left err -> hPrint stderr err >> exitFailure
        Right opb -> return $ Left opb
    ".wbo"  -> do
      ret <- PBFile.parseWBOFile fname
      case ret of
        Left err -> hPrint stderr err >> exitFailure
        Right wbo -> return $ Right wbo
    ext ->
      error $ "unknown file extension: " ++ show ext
  where
    readWCNF = do
      ret <- MaxSAT.parseWCNFFile fname
      case ret of
        Left err -> hPutStrLn stderr err >> exitFailure
        Right wcnf
          | MaxSATNonLinear `elem` o -> return $ Left $ MaxSAT2NLPB.convert wcnf
          | otherwise -> return $ Right $ MaxSAT2WBO.convert wcnf

writePBFile :: [Flag] -> Either PBFile.Formula PBFile.SoftFormula -> IO ()
writePBFile o pb = do
  let objType = last (ObjNone : [t | ObjType t <- o])
  let lp2smtOpt =
        LP2SMT.defaultOptions
        { LP2SMT.optCheckSAT     = not (NoCheck `elem` o)
        , LP2SMT.optProduceModel = not (NoProduceModel `elem` o)
        , LP2SMT.optOptimize     = Optimize `elem` o
        }
  case head ([Just fname | Output fname <- o] ++ [Nothing]) of
    Nothing -> do
      case pb of
        Left opb  -> putStr $ PBFile.showOPB opb ""
        Right wbo -> putStr $ PBFile.showWBO wbo ""
    Just fname -> do
      let opb = case pb of
                  Left opb  -> opb
                  Right wbo -> fst $ WBO2PB.convert wbo
          wbo = case pb of
                  Left opb  -> PB2WBO.convert opb
                  Right wbo -> wbo
          lp  = case pb of
                  Left opb  -> fst $ PB2LP.convert objType opb
                  Right wbo -> fst $ PB2LP.convertWBO (IndicatorConstraint `elem` o) wbo
      case map toLower (takeExtension fname) of
        ".opb" -> writeFile fname (PBFile.showOPB opb "")
        ".wbo" -> writeFile fname (PBFile.showWBO wbo "")
        ".lsp" -> writeFile fname (PB2LSP.convert objType opb "")
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
      lp <- readPBFile o fname
      writePBFile o lp
    (_,_,errs) -> do
      hPutStrLn stderr $ concat errs ++ usageInfo header options
      exitFailure
