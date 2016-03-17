{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  pbconvert
-- Copyright   :  (c) Masahiro Sakai 2012
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
import qualified Data.PseudoBoolean.Attoparsec as PBFileAttoparsec

import qualified ToySolver.Data.MIP as MIP
import qualified ToySolver.Text.GCNF as GCNF
import qualified ToySolver.Text.MaxSAT as MaxSAT
import qualified ToySolver.Text.CNF as CNF
import ToySolver.Converter.ObjType
import qualified ToySolver.Converter.SAT2PB as SAT2PB
import qualified ToySolver.Converter.GCNF2MaxSAT as GCNF2MaxSAT
import qualified ToySolver.Converter.MIP2SMT as MIP2SMT
import qualified ToySolver.Converter.MaxSAT2WBO as MaxSAT2WBO
import qualified ToySolver.Converter.MaxSAT2NLPB as MaxSAT2NLPB
import qualified ToySolver.Converter.PB2IP as PB2IP
import qualified ToySolver.Converter.PBLinearlization as PBLinearlization
import qualified ToySolver.Converter.PB2LSP as PB2LSP
import qualified ToySolver.Converter.PB2WBO as PB2WBO
import qualified ToySolver.Converter.PBSetObj as PBSetObj
import qualified ToySolver.Converter.PB2SMP as PB2SMP
import qualified ToySolver.Converter.PB2SAT as PB2SAT
import qualified ToySolver.Converter.WBO2PB as WBO2PB
import qualified ToySolver.Converter.WBO2MaxSAT as WBO2MaxSAT
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
  , "    pbconvert -o <outputfile> <inputfile>"
  , ""
  , "Supported formats:"
  , "    input: .cnf .wcnf .opb .wbo .gcnf"
  , "    output: .cnf .wcnf .opb .wbo .lsp .lp .mps .smp .smt2 .ys"
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
      ret <- PBFileAttoparsec.parseOPBFile fname
      case ret of
        Left err -> hPutStrLn stderr err >> exitFailure
        Right opb -> return $ Left opb
    ".wbo"  -> do
      ret <- PBFileAttoparsec.parseWBOFile fname
      case ret of
        Left err -> hPutStrLn stderr err >> exitFailure
        Right wbo -> return $ Right wbo
    ".gcnf" -> do
      ret <- GCNF.parseFile fname
      case ret of
        Left err -> hPutStrLn stderr err >> exitFailure
        Right gcnf -> return $ fromWCNF $ GCNF2MaxSAT.convert gcnf
    ext ->
      error $ "unknown file extension: " ++ show ext
  where    
    readWCNF = do
      ret <- MaxSAT.parseFile fname
      case ret of
        Left err -> hPutStrLn stderr err >> exitFailure
        Right wcnf -> return $ fromWCNF wcnf
    fromWCNF wcnf
      | MaxSATNonLinear `elem` o = Left $ MaxSAT2NLPB.convert wcnf
      | otherwise = Right $ MaxSAT2WBO.convert wcnf

transformPBFile :: [Flag] -> Either PBFile.Formula PBFile.SoftFormula -> Either PBFile.Formula PBFile.SoftFormula
transformPBFile o = transformObj o . transformPBLinearlization o

transformObj :: [Flag] -> Either PBFile.Formula PBFile.SoftFormula -> Either PBFile.Formula PBFile.SoftFormula
transformObj o pb =
  case pb of
    Left opb | isNothing (PBFile.pbObjectiveFunction opb) -> Left $ PBSetObj.setObj objType opb
    _ -> pb
  where
    objType = last (ObjNone : [t | ObjType t <- o])

transformPBLinearlization :: [Flag] -> Either PBFile.Formula PBFile.SoftFormula -> Either PBFile.Formula PBFile.SoftFormula
transformPBLinearlization o pb
  | Linearlization `elem` o =
      case pb of
        Left opb  -> Left  $ PBLinearlization.linearlize    opb (LinearlizationUsingPB `elem` o)
        Right wbo -> Right $ PBLinearlization.linearlizeWBO wbo (LinearlizationUsingPB `elem` o)
  | otherwise = pb

writePBFile :: [Flag] -> Either PBFile.Formula PBFile.SoftFormula -> IO ()
writePBFile o pb = do
  let mip2smtOpt =
        def
        { MIP2SMT.optSetLogic     = listToMaybe [logic | SMTSetLogic logic <- o]
        , MIP2SMT.optCheckSAT     = not (SMTNoCheck `elem` o)
        , MIP2SMT.optProduceModel = not (SMTNoProduceModel `elem` o)
        , MIP2SMT.optOptimize     = SMTOptimize `elem` o
        }
  case head ([Just fname | Output fname <- o] ++ [Nothing]) of
    Nothing -> do
      hSetBinaryMode stdout True
      hSetBuffering stdout (BlockBuffering Nothing)
      case pb of
        Left opb  -> PBFile.hPutOPB stdout opb
        Right wbo -> PBFile.hPutWBO stdout wbo
    Just fname -> do
      let opb = case pb of
                  Left opb  -> opb
                  Right wbo ->
                    case WBO2PB.convert wbo of
                      (opb, _, _)
                        | Linearlization `elem` o ->
                            -- WBO->OPB conversion may have introduced non-linearity
                            PBLinearlization.linearlize opb (LinearlizationUsingPB `elem` o)
			| otherwise -> opb
          wbo = case pb of
                  Left opb  -> PB2WBO.convert opb
                  Right wbo -> wbo
          lp  = case pb of
                  Left opb  ->
                    case PB2IP.convert opb of
                      (ip, _, _) -> ip
                  Right wbo ->
                    case PB2IP.convertWBO (IndicatorConstraint `elem` o) wbo of
                      (ip, _, _) -> ip
          lsp = case pb of
                  Left opb  -> PB2LSP.convert opb
                  Right wbo -> PB2LSP.convertWBO wbo
      case map toLower (takeExtension fname) of
        ".opb" -> PBFile.writeOPBFile fname opb
        ".wbo" -> PBFile.writeWBOFile fname wbo
        ".cnf" ->
          case PB2SAT.convert opb of
	    (cnf, _, _) -> CNF.writeFile fname cnf
        ".wcnf" ->
          case WBO2MaxSAT.convert wbo of
            (wcnf, _, _) -> MaxSAT.writeFile fname wcnf
        ".lsp" -> writeFile fname (lsp "")
        ".lp" -> MIP.writeLPFile fname lp
        ".mps" -> MIP.writeMPSFile fname lp
        ".smp" -> do
          writeFile fname (PB2SMP.convert False opb "")
        ".smt2" -> do
          writeFile fname (MIP2SMT.convert mip2smtOpt lp "")
        ".ys" -> do
          let lang = MIP2SMT.YICES (if Yices2 `elem` o then MIP2SMT.Yices2 else MIP2SMT.Yices1)
          writeFile fname (MIP2SMT.convert mip2smtOpt{ MIP2SMT.optLanguage = lang } lp "")
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
      pb <- readPBFile o fname
      let pb2 = transformPBFile o pb
      writePBFile o pb2
    (_,_,errs) -> do
      hPutStrLn stderr $ concat errs ++ usageInfo header options
      exitFailure
