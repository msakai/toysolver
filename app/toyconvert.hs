{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  toyconvert
-- Copyright   :  (c) Masahiro Sakai 2012-2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
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

import qualified ToySolver.Data.MIP as MIP
import ToySolver.Converter
import ToySolver.Converter.ObjType
import qualified ToySolver.Converter.MIP2SMT as MIP2SMT
import qualified ToySolver.Converter.PBSetObj as PBSetObj
import qualified ToySolver.FileFormat as FF
import qualified ToySolver.QUBO as QUBO
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
      [ PP.text "input:"  <+> (PP.align $ PP.fillSep $ map PP.text $ words ".cnf .wcnf .opb .wbo .gcnf .lp .mps .qubo")
      , PP.text "output:" <+> (PP.align $ PP.fillSep $ map PP.text $ words ".cnf .wcnf .opb .wbo .lsp .lp .mps .smp .smt2 .ys .qubo")
      ]
  ]

data Problem
  = ProbOPB PBFile.Formula
  | ProbWBO PBFile.SoftFormula
  | ProbMIP (MIP.Problem Scientific)

readProblem :: Options -> String -> IO Problem
readProblem o fname = do
  enc <- T.mapM mkTextEncoding (optFileEncoding o)
  case getExt fname of
    ".cnf"
      | optAsMaxSAT o ->
          liftM (ProbWBO . fst . maxsat2wbo) $ FF.readFile fname
      | otherwise -> do
          liftM (ProbOPB . fst . sat2pb) $ FF.readFile fname
    ".wcnf" ->
      liftM (ProbWBO . fst . maxsat2wbo) $ FF.readFile fname
    ".opb"  -> liftM ProbOPB $ FF.readFile fname
    ".wbo"  -> liftM ProbWBO $ FF.readFile fname
    ".gcnf" ->
      liftM (ProbWBO . fst . maxsat2wbo . fst . gcnf2maxsat) $ FF.readFile fname
    ".lp"   -> ProbMIP <$> MIP.readLPFile def{ MIP.optFileEncoding = enc } fname
    ".mps"  -> ProbMIP <$> MIP.readMPSFile def{ MIP.optFileEncoding = enc } fname
    ".qubo" -> do
      (qubo :: QUBO.Problem Scientific) <- FF.readFile fname
      return $ ProbOPB $ fst $ qubo2pb qubo
    ext ->
      error $ "unknown file extension: " ++ show ext

getExt :: String -> String
getExt name | (base, ext) <- splitExtension name =
  case map toLower ext of
#ifdef WITH_ZLIB
    ".gz" -> getExt base
#endif
    s -> s

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
        ProbOPB opb -> ProbOPB $ fst $ linearizePB  opb (optLinearizationUsingPB o)
        ProbWBO wbo -> ProbWBO $ fst $ linearizeWBO wbo (optLinearizationUsingPB o)
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
        ProbOPB opb -> ByteStringBuilder.hPutBuilder stdout $ FF.render opb
        ProbWBO wbo -> ByteStringBuilder.hPutBuilder stdout $ FF.render wbo
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
                    case wbo2pb wbo of
                      (opb, _)
                        | optLinearization o ->
                            -- WBO->OPB conversion may have introduced non-linearity
                            fst $ linearizePB opb (optLinearizationUsingPB o)
                        | otherwise -> opb
                  ProbMIP mip ->
                    case mip2pb (fmap toRational mip) of
                      Left err -> error err
                      Right (opb, _) -> opb
          wbo = case problem of
                  ProbOPB opb -> fst $ pb2wbo opb
                  ProbWBO wbo -> wbo
                  ProbMIP _   -> fst $ pb2wbo opb
          lp  = case problem of
                  ProbOPB opb ->
                    case pb2ip opb of
                      (ip, _) -> fmap fromInteger ip
                  ProbWBO wbo ->
                    case wbo2ip (optIndicatorConstraint o) wbo of
                      (ip, _) -> fmap fromInteger ip
                  ProbMIP mip -> mip
          lsp = case problem of
                  ProbOPB opb -> pb2lsp opb
                  ProbWBO wbo -> wbo2lsp wbo
                  ProbMIP _   -> pb2lsp opb
      case getExt fname of
        ".opb" -> FF.writeFile fname $ normalizePB opb
        ".wbo" -> FF.writeFile fname $ normalizeWBO wbo
        ".cnf" ->
          case pb2sat opb of
            (cnf, _) ->
              case optKSat o of
                Nothing -> FF.writeFile fname cnf
                Just k ->
                  let (cnf2, _) = sat2ksat k cnf
                  in FF.writeFile fname cnf2
        ".wcnf" ->
          case wbo2maxsat wbo of
            (wcnf, _) -> FF.writeFile fname wcnf
        ".lsp" ->
          withBinaryFile fname WriteMode $ \h ->
            ByteStringBuilder.hPutBuilder h lsp
        ".lp" -> MIP.writeLPFile def{ MIP.optFileEncoding = enc } fname lp
        ".mps" -> MIP.writeMPSFile def{ MIP.optFileEncoding = enc } fname lp
        ".smp" -> do
          withBinaryFile fname WriteMode $ \h ->
            ByteStringBuilder.hPutBuilder h (pb2smp False opb)
        ".smt2" -> do
          withFile fname WriteMode $ \h -> do
            F.mapM_ (hSetEncoding h) enc
            TLIO.hPutStr h $ TextBuilder.toLazyText $
              MIP2SMT.mip2smt mip2smtOpt (fmap toRational lp)
        ".ys" -> do
          let lang = MIP2SMT.YICES (if optYices2 o then MIP2SMT.Yices2 else MIP2SMT.Yices1)
          withFile fname WriteMode $ \h -> do
            F.mapM_ (hSetEncoding h) enc
            TLIO.hPutStr h $ TextBuilder.toLazyText $
              MIP2SMT.mip2smt mip2smtOpt{ MIP2SMT.optLanguage = lang } (fmap toRational lp)
        ".qubo" ->
          case pb2qubo opb of
            ((qubo, _th), _) -> FF.writeFile fname (fmap (fromInteger :: Integer -> Scientific) qubo)
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
