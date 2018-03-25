{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  toyconvert
-- Copyright   :  (c) Masahiro Sakai 2012-2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (CPP)
--
-----------------------------------------------------------------------------

module Main where

import Control.Applicative
import Control.Monad
import qualified Data.ByteString.Builder as ByteStringBuilder
import Data.Char
import Data.Default.Class
import qualified Data.Foldable as F
import Data.Maybe
import Data.Monoid
import Data.Scientific (Scientific)
import qualified Data.Text.Lazy.Builder as TextBuilder
import qualified Data.Text.Lazy.IO as TLIO
import qualified Data.Traversable as T
import qualified Data.Version as V
import Options.Applicative
import System.IO
import System.Exit
import System.FilePath
import Text.PrettyPrint.ANSI.Leijen ((<+>))
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified Data.PseudoBoolean as PBFile
import qualified Data.PseudoBoolean.Attoparsec as PBFileAttoparsec

import qualified ToySolver.Data.MIP as MIP
import qualified ToySolver.Text.CNF as CNF
import ToySolver.Converter.ObjType
import qualified ToySolver.Converter.SAT2PB as SAT2PB
import qualified ToySolver.Converter.GCNF2MaxSAT as GCNF2MaxSAT
import qualified ToySolver.Converter.MIP2PB as MIP2PB
import qualified ToySolver.Converter.MIP2SMT as MIP2SMT
import qualified ToySolver.Converter.MaxSAT2WBO as MaxSAT2WBO
import qualified ToySolver.Converter.PB2IP as PB2IP
import qualified ToySolver.Converter.PBLinearization as PBLinearization
import ToySolver.Converter.PBNormalization
import qualified ToySolver.Converter.PB2LSP as PB2LSP
import qualified ToySolver.Converter.PB2WBO as PB2WBO
import qualified ToySolver.Converter.PBSetObj as PBSetObj
import qualified ToySolver.Converter.PB2SMP as PB2SMP
import qualified ToySolver.Converter.PB2SAT as PB2SAT
import qualified ToySolver.Converter.SAT2KSAT as SAT2KSAT
import qualified ToySolver.Converter.WBO2PB as WBO2PB
import qualified ToySolver.Converter.WBO2MaxSAT as WBO2MaxSAT
import ToySolver.Version
import ToySolver.Internal.Util (setEncodingChar8)

data Options = Options
  { optInput  :: FilePath
  , optOutput :: Maybe FilePath
  , optAsMaxSAT :: Bool
  , optObjType :: ObjType
  , optIndicatorConstraint :: Bool
  , optSMTSetLogic :: Maybe String
  , optSMTOptimize :: Bool
  , optSMTNoCheck :: Bool
  , optSMTNoProduceModel :: Bool
  , optYices2 :: Bool
  , optLinearization :: Bool
  , optLinearizationUsingPB :: Bool
  , optKSat :: Maybe Int
  , optFileEncoding :: Maybe String
  , optRemoveUserCuts :: Bool
  } deriving (Eq, Show)

optionsParser :: Parser Options
optionsParser = Options
  <$> fileInput
  <*> outputOption
  <*> maxsatOption
  <*> objOption
  <*> indicatorConstraintOption
  <*> smtSetLogicOption
  <*> smtOptimizeOption
  <*> smtNoCheckOption
  <*> smtNoProduceModelOption
  <*> yices2Option
  <*> linearizationOption
  <*> linearizationPBOption
  <*> kSATOption
  <*> encodingOption
  <*> removeUserCutsOption
  where
    fileInput :: Parser FilePath
    fileInput = argument str (metavar "FILE")

    outputOption :: Parser (Maybe FilePath)
    outputOption = optional $ strOption
      $  long "output"
      <> short 'o'
      <> metavar "FILE"
      <> help "output filename"

    maxsatOption :: Parser Bool
    maxsatOption = switch
      $  long "maxsat"
      <> help "treat *.cnf file as MAX-SAT problem"

    objOption :: Parser ObjType
    objOption = option parseObjType
      $  long "obj"
      <> metavar "STR"
      <> help "objective function for SAT/PBS: none (default), max-one, max-zero"
      <> value ObjNone
      <> showDefaultWith showObjType
      where
        showObjType :: ObjType -> String
        showObjType ObjNone    = "none"
        showObjType ObjMaxOne  = "max-one"
        showObjType ObjMaxZero = "max-zero"

        parseObjType :: ReadM ObjType
        parseObjType = eitherReader $ \s ->
          case map toLower s of
            "none"     -> return ObjNone
            "max-one"  -> return ObjMaxOne
            "max-zero" -> return ObjMaxZero
            _          -> Left ("unknown obj: " ++ s)

    indicatorConstraintOption :: Parser Bool
    indicatorConstraintOption = switch
      $  long "indicator"
      <> help "use indicator constraints in output LP file"

    smtSetLogicOption :: Parser (Maybe String)
    smtSetLogicOption = optional $ strOption
      $  long "smt-set-logic"
      <> metavar "STR"
      <> help "output \"(set-logic STR)\""

    smtOptimizeOption :: Parser Bool
    smtOptimizeOption = switch
      $  long "smt-optimize"
      <> help "output optimiality condition which uses quantifiers"

    smtNoCheckOption :: Parser Bool
    smtNoCheckOption = switch
      $  long "smt-no-check"
      <> help "do not output \"(check)\""

    smtNoProduceModelOption :: Parser Bool
    smtNoProduceModelOption = switch
      $  long "smt-no-produce-model"
      <> help "do not output \"(set-option :produce-models true)\""

    yices2Option :: Parser Bool
    yices2Option = switch
      $  long "yices2"
      <> help "output for yices2 rather than yices1"

    linearizationOption :: Parser Bool
    linearizationOption = switch
      $  long "linearize"
      <> help "linearize nonlinear pseudo-boolean constraints"

    linearizationPBOption :: Parser Bool
    linearizationPBOption = switch
      $  long "linearizer-pb"
      <> help "Use PB constraint in linearization"

    kSATOption :: Parser (Maybe Int)
    kSATOption = optional $ option auto
      $  long "ksat"
      <> metavar "INT"
      <> help "generate k-SAT formula when outputing .cnf file"

    encodingOption :: Parser (Maybe String)
    encodingOption = optional $ strOption
      $  long "encoding"
      <> metavar "ENCODING"
      <> help "file encoding for LP/MPS files"

    removeUserCutsOption :: Parser Bool
    removeUserCutsOption = switch
      $  long "remove-usercuts"
      <> help "remove user-defined cuts from LP/MPS files"

parserInfo :: ParserInfo Options
parserInfo = info (helper <*> versionOption <*> optionsParser)
  $  fullDesc
  <> header "toyconvert - converter between various kind of problem files"
  <> footerDoc (Just supportedFormatsDoc)
  where
    versionOption :: Parser (a -> a)
    versionOption = infoOption (V.showVersion version)
      $  hidden
      <> long "version"
      <> help "Show version"

supportedFormatsDoc :: PP.Doc
supportedFormatsDoc =
  PP.vsep
  [ PP.text "Supported formats:"
  , PP.indent 2 $ PP.vsep
      [ PP.text "input:"  <+> (PP.align $ PP.fillSep $ map PP.text $ words ".cnf .wcnf .opb .wbo .gcnf .lp .mps")
      , PP.text "output:" <+> (PP.align $ PP.fillSep $ map PP.text $ words ".cnf .wcnf .opb .wbo .lsp .lp .mps .smp .smt2 .ys")
      ]
  ]

data Problem
  = ProbOPB PBFile.Formula
  | ProbWBO PBFile.SoftFormula
  | ProbMIP (MIP.Problem Scientific)

readProblem :: Options -> String -> IO Problem
readProblem o fname = do
  enc <- T.mapM mkTextEncoding (optFileEncoding o)
  case map toLower (takeExtension fname) of
    ".cnf"
      | optAsMaxSAT o ->
          liftM (ProbWBO . MaxSAT2WBO.convert) $ CNF.readFile fname
      | otherwise -> do
          liftM (ProbOPB . SAT2PB.convert) $ CNF.readFile fname
    ".wcnf" ->
      liftM (ProbWBO . MaxSAT2WBO.convert) $ CNF.readFile fname
    ".opb"  -> do
      ret <- PBFileAttoparsec.parseOPBFile fname
      case ret of
        Left err -> hPutStrLn stderr err >> exitFailure
        Right opb -> return $ ProbOPB opb
    ".wbo"  -> do
      ret <- PBFileAttoparsec.parseWBOFile fname
      case ret of
        Left err -> hPutStrLn stderr err >> exitFailure
        Right wbo -> return $ ProbWBO wbo
    ".gcnf" ->
      liftM (ProbWBO . MaxSAT2WBO.convert . GCNF2MaxSAT.convert) $ CNF.readFile fname
    ".lp"   -> ProbMIP <$> MIP.readLPFile def{ MIP.optFileEncoding = enc } fname
    ".mps"  -> ProbMIP <$> MIP.readMPSFile def{ MIP.optFileEncoding = enc } fname
    ext ->
      error $ "unknown file extension: " ++ show ext

transformProblem :: Options -> Problem -> Problem
transformProblem o = transformObj o . transformPBLinearization o . transformMIPRemoveUserCuts o

transformObj :: Options -> Problem -> Problem
transformObj o problem =
  case problem of
    ProbOPB opb | isNothing (PBFile.pbObjectiveFunction opb) -> ProbOPB $ PBSetObj.setObj (optObjType o) opb
    _ -> problem

transformPBLinearization :: Options -> Problem -> Problem
transformPBLinearization o problem
  | optLinearization o =
      case problem of
        ProbOPB opb -> ProbOPB $ PBLinearization.linearize    opb (optLinearizationUsingPB o)
        ProbWBO wbo -> ProbWBO $ PBLinearization.linearizeWBO wbo (optLinearizationUsingPB o)
        ProbMIP mip -> ProbMIP mip
  | otherwise = problem

transformMIPRemoveUserCuts :: Options -> Problem -> Problem
transformMIPRemoveUserCuts o problem
  | optRemoveUserCuts o =
      case problem of
        ProbMIP mip -> ProbMIP $ mip{ MIP.userCuts = [] }
        _ -> problem
  | otherwise = problem

writeProblem :: Options -> Problem -> IO ()
writeProblem o problem = do
  enc <- T.mapM mkTextEncoding (optFileEncoding o)
  let mip2smtOpt =
        def
        { MIP2SMT.optSetLogic     = optSMTSetLogic o
        , MIP2SMT.optCheckSAT     = not (optSMTNoCheck o)
        , MIP2SMT.optProduceModel = not (optSMTNoProduceModel o)
        , MIP2SMT.optOptimize     = optSMTOptimize o
        }
  case optOutput o of
    Nothing -> do
      hSetBinaryMode stdout True
      hSetBuffering stdout (BlockBuffering Nothing)
      case problem of
        ProbOPB opb -> PBFile.hPutOPB stdout opb
        ProbWBO wbo -> PBFile.hPutWBO stdout wbo
        ProbMIP mip -> do
          case MIP.toLPString def mip of
            Left err -> hPutStrLn stderr ("conversion failure: " ++ err) >> exitFailure
            Right s -> do
              F.mapM_ (hSetEncoding stdout) enc
              TLIO.hPutStr stdout s
    Just fname -> do
      let opb = case problem of
                  ProbOPB opb -> opb
                  ProbWBO wbo ->
                    case WBO2PB.convert wbo of
                      (opb, _, _)
                        | optLinearization o ->
                            -- WBO->OPB conversion may have introduced non-linearity
                            PBLinearization.linearize opb (optLinearizationUsingPB o)
                        | otherwise -> opb
                  ProbMIP mip ->
                    case MIP2PB.convert (fmap toRational mip) of
                      Left err -> error err
                      Right (opb, _, _) -> opb
          wbo = case problem of
                  ProbOPB opb -> PB2WBO.convert opb
                  ProbWBO wbo -> wbo
                  ProbMIP _   -> PB2WBO.convert opb
          lp  = case problem of
                  ProbOPB opb ->
                    case PB2IP.convert opb of
                      (ip, _, _) -> fmap fromInteger ip
                  ProbWBO wbo ->
                    case PB2IP.convertWBO (optIndicatorConstraint o) wbo of
                      (ip, _, _) -> fmap fromInteger ip
                  ProbMIP mip -> mip
          lsp = case problem of
                  ProbOPB opb -> PB2LSP.convert opb
                  ProbWBO wbo -> PB2LSP.convertWBO wbo
                  ProbMIP _   -> PB2LSP.convert opb
      case map toLower (takeExtension fname) of
        ".opb" -> PBFile.writeOPBFile fname $ normalizeOPB opb
        ".wbo" -> PBFile.writeWBOFile fname $ normalizeWBO wbo
        ".cnf" ->
          case PB2SAT.convert opb of
            (cnf, _, _) ->
              case optKSat o of
                Nothing -> CNF.writeFile fname cnf
                Just k ->
                  let (cnf2, _, _) = SAT2KSAT.convert k cnf
                  in CNF.writeFile fname cnf2
        ".wcnf" ->
          case WBO2MaxSAT.convert wbo of
            (wcnf, _, _) -> CNF.writeFile fname wcnf
        ".lsp" ->
          withBinaryFile fname WriteMode $ \h ->
            ByteStringBuilder.hPutBuilder h lsp
        ".lp" -> MIP.writeLPFile def{ MIP.optFileEncoding = enc } fname lp
        ".mps" -> MIP.writeMPSFile def{ MIP.optFileEncoding = enc } fname lp
        ".smp" -> do
          withBinaryFile fname WriteMode $ \h ->
            ByteStringBuilder.hPutBuilder h (PB2SMP.convert False opb)
        ".smt2" -> do
          withFile fname WriteMode $ \h -> do
            F.mapM_ (hSetEncoding h) enc
            TLIO.hPutStr h $ TextBuilder.toLazyText $
              MIP2SMT.convert mip2smtOpt (fmap toRational lp)
        ".ys" -> do
          let lang = MIP2SMT.YICES (if optYices2 o then MIP2SMT.Yices2 else MIP2SMT.Yices1)
          withFile fname WriteMode $ \h -> do
            F.mapM_ (hSetEncoding h) enc
            TLIO.hPutStr h $ TextBuilder.toLazyText $
              MIP2SMT.convert mip2smtOpt{ MIP2SMT.optLanguage = lang } (fmap toRational lp)
        ext -> do
          error $ "unknown file extension: " ++ show ext

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif

  opt <- execParser parserInfo
  prob <- readProblem opt (optInput opt)
  let prob2 = transformProblem opt prob
  writeProblem opt prob2
