{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  lpconvert
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (CPP)
--
-----------------------------------------------------------------------------

module Main where

import Data.Char
import Data.Default.Class
import Data.Maybe
import qualified Data.Version as V
import System.Environment
import System.IO
import System.Exit
import System.FilePath
import System.Console.GetOpt
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS

import qualified Data.PseudoBoolean as PBFile

import qualified ToySolver.Data.MIP as MIP
import qualified ToySolver.Text.GCNF as GCNF
import qualified ToySolver.Text.MaxSAT as MaxSAT
import ToySolver.Converter.ObjType
import qualified ToySolver.Converter.GCNF2MaxSAT as GCNF2MaxSAT
import qualified ToySolver.Converter.MIP2SMT as MIP2SMT
import qualified ToySolver.Converter.MaxSAT2IP as MaxSAT2IP
import qualified ToySolver.Converter.MaxSAT2NLPB as MaxSAT2NLPB
import qualified ToySolver.Converter.PB2IP as PB2IP
import qualified ToySolver.Converter.PBLinearlization as PBLinearlization
import qualified ToySolver.Converter.PBSetObj as PBSetObj
import qualified ToySolver.Converter.SAT2PB as SAT2PB
import ToySolver.Version
import ToySolver.Internal.Util (setEncodingChar8)

data Flag
  = Help
  | Version
  | Output String
  | AsMaxSAT
  | ObjType ObjType
  | IndicatorConstraint
  | SMTSetLogic String
  | SMTOptimize
  | SMTNoCheck
  | SMTNoProduceModel
  | MaxSATNonLinear
  | Yices2
  | Linearlization
  | LinearlizationUsingPB
  deriving Eq

options :: [OptDescr Flag]
options =
    [ Option ['h'] ["help"] (NoArg Help) "show help"
    , Option ['v'] ["version"] (NoArg Version)         "show version number"
    , Option ['o'] [] (ReqArg Output "FILE") "output filename"
    , Option []    ["maxsat"]  (NoArg AsMaxSAT)  "treat *.cnf file as MAX-SAT problem"
    , Option []    ["obj"] (ReqArg (ObjType . parseObjType) "STRING") "objective function for SAT/PBS: none (default), max-one, max-zero"
    , Option []    ["indicator"] (NoArg IndicatorConstraint) "use indicator constraints in output LP file"
    , Option []    ["smt-set-logic"] (ReqArg SMTSetLogic "STRING")　"output \"(set-logic STRING)\""
    , Option []    ["smt-optimize"] (NoArg SMTOptimize)   "output optimiality condition which uses quantifiers"
    , Option []    ["smt-no-check"] (NoArg SMTNoCheck)    "do not output \"(check)\""
    , Option []    ["smt-no-produce-model"] (NoArg SMTNoProduceModel) "do not output \"(set-option :produce-models true)\""    
    , Option []    ["maxsat-nonlinear"] (NoArg MaxSATNonLinear) "use non-linear formulation of Max-SAT"
    , Option []    ["yices2"] (NoArg Yices2) "output for yices2 rather than yices1"
    , Option []    ["linearlize"] (NoArg Linearlization) "linearliza nonlinear pseudo-boolean constraints"
    , Option []    ["linearizer-pb"] (NoArg LinearlizationUsingPB) "Use PB constraint in linearization"
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
  , "    output: .lp .mps .smt2 .ys"
  , ""
  , "Options:"
  ]

readLP :: [Flag] -> String -> IO MIP.Problem
readLP o fname = do
  case map toLower (takeExtension fname) of
    ".cnf"
      | AsMaxSAT `elem` o -> readWCNF
      | otherwise -> do
          ret <- DIMACS.parseFile fname
          case ret of
            Left err -> hPrint stderr err >> exitFailure
            Right cnf -> do
              let pb = transformPBFile o $ SAT2PB.convert cnf
              let (mip, _, _) = PB2IP.convert pb
              return mip
    ".wcnf" -> readWCNF
    ".gcnf" -> do
      ret <- GCNF.parseFile fname
      case ret of
        Left err -> hPutStrLn stderr err >> exitFailure
        Right gcnf -> return $ fromWCNF $ GCNF2MaxSAT.convert gcnf
    ".opb"  -> do
      ret <- PBFile.parseOPBFile fname
      case ret of
        Left err -> hPrint stderr err >> exitFailure
        Right formula -> do
          let pb = transformPBFile o formula
          let (mip, _, _) = PB2IP.convert pb
          return mip
    ".wbo"  -> do
      ret <- PBFile.parseWBOFile fname
      case ret of
        Left err -> hPrint stderr err >> exitFailure
        Right formula -> do
          let (mip, _, _) = PB2IP.convertWBO (IndicatorConstraint `elem` o) formula
          return mip
    ".lp"   -> do
      ret <- MIP.readLPFile fname
      case ret of
        Left err -> hPrint stderr err >> exitFailure
        Right mip -> return mip
    ".mps"  -> do
      ret <- MIP.readMPSFile fname
      case ret of
        Left err -> hPrint stderr err >> exitFailure
        Right mip -> return mip
    ext ->
      error $ "unknown file extension: " ++ show ext
  where
    readWCNF = do
      ret <- MaxSAT.parseFile fname
      case ret of
        Left err -> hPutStrLn stderr err >> exitFailure
        Right wcnf -> return $ fromWCNF wcnf
    fromWCNF wcnf
      | MaxSATNonLinear `elem` o =
          let pb = transformPBFile o $ MaxSAT2NLPB.convert wcnf
              (mip, _, _) = PB2IP.convert pb
          in mip
      | otherwise =
          let (mip, _, _) = MaxSAT2IP.convert (IndicatorConstraint `elem` o) wcnf
          in mip

transformPBFile :: [Flag] -> PBFile.Formula -> PBFile.Formula
transformPBFile o = transformObj o . transformPBLinearlization o

transformObj :: [Flag] -> PBFile.Formula -> PBFile.Formula
transformObj o opb | isNothing (PBFile.pbObjectiveFunction opb) = PBSetObj.setObj objType opb
  where
    objType = last (ObjNone : [t | ObjType t <- o])
transformObj _ opb = opb

transformPBLinearlization :: [Flag] -> PBFile.Formula -> PBFile.Formula
transformPBLinearlization o opb = PBLinearlization.linearlize    opb (LinearlizationUsingPB `elem` o)

writeLP :: [Flag] -> MIP.Problem -> IO ()
writeLP o mip = do
  let mip2smtOpt =
        def
        { MIP2SMT.optSetLogic     = listToMaybe [logic | SMTSetLogic logic <- o]
        , MIP2SMT.optCheckSAT     = not (SMTNoCheck `elem` o)
        , MIP2SMT.optProduceModel = not (SMTNoProduceModel `elem` o)
        , MIP2SMT.optOptimize     = SMTOptimize `elem` o
        }

  case head ([Just fname | Output fname <- o] ++ [Nothing]) of
    Nothing -> 
      case MIP.toLPString mip of
        Left err -> hPutStrLn stderr ("conversion failure: " ++ err) >> exitFailure
        Right s -> putStr s
    Just fname -> do
      case map toLower (takeExtension fname) of
        ".lp" -> MIP.writeLPFile fname mip
        ".mps" -> MIP.writeMPSFile fname mip
        ".smt2" -> do
          writeFile fname (MIP2SMT.convert mip2smtOpt mip "")
        ".ys" -> do
          let lang = MIP2SMT.YICES (if Yices2 `elem` o then MIP2SMT.Yices2 else MIP2SMT.Yices1)
          writeFile fname (MIP2SMT.convert mip2smtOpt{ MIP2SMT.optLanguage = lang } mip "")
        ext -> do
          error $ "unknown file extension: " ++ show ext

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif

  args <- getArgs
  case getOpt Permute options args of
    (o,_,[])
      | Help `elem` o    -> putStrLn (usageInfo header options)
      | Version `elem` o -> putStrLn (V.showVersion version)
    (o,[fname],[]) -> do
      mip <- readLP o fname
      writeLP o mip
    (_,_,errs) -> do
      hPutStrLn stderr $ concat errs ++ usageInfo header options
      exitFailure
