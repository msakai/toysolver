{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
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
import qualified Data.Aeson as J
import qualified Data.ByteString.Builder as ByteStringBuilder
import Data.Char
import Data.Default.Class
import qualified Data.Foldable as F
import Data.List (intercalate)
import Data.Map.Lazy (Map)
import Data.Maybe
import Data.Scientific (Scientific)
import qualified Data.Text.Lazy.Builder as TextBuilder
import qualified Data.Text.Lazy.IO as TLIO
import qualified Data.Traversable as T
import qualified Data.Version as V
import Options.Applicative hiding (info)
import qualified Options.Applicative
import System.IO
import System.Exit
#if MIN_VERSION_optparse_applicative(0,18,0)
import Prettyprinter ((<+>))
import qualified Prettyprinter as PP
#else
import Text.PrettyPrint.ANSI.Leijen ((<+>))
import qualified Text.PrettyPrint.ANSI.Leijen as PP
#endif

import qualified Data.PseudoBoolean as PBFile
import qualified Numeric.Optimization.MIP as MIP

import ToySolver.Converter
import qualified ToySolver.Converter.MIP2SMT as MIP2SMT
import qualified ToySolver.FileFormat as FF
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.QUBO as QUBO
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Encoder.PB as PB
import ToySolver.Version
import ToySolver.Internal.Util (setEncodingChar8)

data Options = Options
  { optInput  :: FilePath
  , optOutput :: Maybe FilePath
  , optInfoOutput :: Maybe FilePath
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
  , optMPSObjName :: Bool
  , optRemoveUserCuts :: Bool
  , optNewWCNF :: Bool
  , optPBFastParser :: Bool
  , optPBEncoding :: PB.Strategy
  } deriving (Eq, Show)

optionsParser :: Parser Options
optionsParser = Options
  <$> fileInput
  <*> outputOption
  <*> infoOutputOption
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
  <*> mpsObjNameOption
  <*> removeUserCutsOption
  <*> newWCNFOption
  <*> pbFastParserOption
  <*> pbEncoding
  where
    fileInput :: Parser FilePath
    fileInput = argument str (metavar "FILE")

    outputOption :: Parser (Maybe FilePath)
    outputOption = optional $ strOption
      $  long "output"
      <> short 'o'
      <> metavar "FILE"
      <> help "output filename"

    infoOutputOption :: Parser (Maybe FilePath)
    infoOutputOption = optional $ strOption
      $  long "dump-info"
      <> metavar "FILE"
      <> help "filename for dumping conversion information"

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

    mpsObjNameOption :: Parser Bool
    mpsObjNameOption = asum
      [ flag' True
          (  long "mps-obj-name"
          <> help ("Write OBJNAME section in MPS file" ++ (if MIP.optMPSWriteObjName def then " (default)" else "")))
      , flag' False
          (  long "no-mps-obj-name"
          <> help ("Do not write OBJNAME section in MPS file" ++ (if MIP.optMPSWriteObjName def then "" else " (default)")))
      , pure (MIP.optMPSWriteObjName def)
      ]

    removeUserCutsOption :: Parser Bool
    removeUserCutsOption = switch
      $  long "remove-usercuts"
      <> help "remove user-defined cuts from LP/MPS files"

    newWCNFOption :: Parser Bool
    newWCNFOption = switch
      $  long "wcnf-new"
      <> help "use new format for writing WCNF files"

    pbFastParserOption :: Parser Bool
    pbFastParserOption = switch
      $  long "pb-fast-parser"
      <> help "use attoparsec-based parser instead of megaparsec-based one for speed"

    pbEncoding :: Parser PB.Strategy
    pbEncoding = option (maybeReader PB.parseStrategy)
      $  long "pb-encoding"
      <> metavar "STR"
      <> help ("PB to SAT encoding: " ++ intercalate ", " [PB.showStrategy m | m <- [minBound..maxBound]])
      <> value def
      <> showDefaultWith PB.showStrategy

parserInfo :: ParserInfo Options
parserInfo = Options.Applicative.info (helper <*> versionOption <*> optionsParser)
  $  fullDesc
  <> header "toyconvert - converter between various kind of problem files"
  <> footerDoc (Just supportedFormatsDoc)
  where
    versionOption :: Parser (a -> a)
    versionOption = infoOption (V.showVersion version)
      $  hidden
      <> long "version"
      <> help "Show version"

#if MIN_VERSION_optparse_applicative(0,18,0)

supportedFormatsDoc :: PP.Doc ann
supportedFormatsDoc =
  PP.vsep
  [ PP.pretty "Supported formats:"
  , PP.indent 2 $ PP.vsep
      [ PP.pretty "input:"  <+> (PP.align $ PP.fillSep $ map PP.pretty $ words ".cnf .wcnf .opb .wbo .gcnf .lp .mps .qubo")
      , PP.pretty "output:" <+> (PP.align $ PP.fillSep $ map PP.pretty $ words ".cnf .wcnf .opb .wbo .lsp .lp .mps .smp .smt2 .ys .qubo")
      ]
  ]

#else

supportedFormatsDoc :: PP.Doc
supportedFormatsDoc =
  PP.vsep
  [ PP.text "Supported formats:"
  , PP.indent 2 $ PP.vsep
      [ PP.text "input:"  <+> (PP.align $ PP.fillSep $ map PP.text $ words ".cnf .wcnf .opb .wbo .gcnf .lp .mps .qubo")
      , PP.text "output:" <+> (PP.align $ PP.fillSep $ map PP.text $ words ".cnf .wcnf .opb .wbo .lsp .lp .mps .smp .smt2 .ys .qubo")
      ]
  ]

#endif

data Trail sol where
  Trail :: (Transformer a, J.ToJSON a) => a -> Trail (Target a)

data Problem
  = ProbOPB PBFile.Formula (Trail SAT.Model)
  | ProbWBO PBFile.SoftFormula (Trail SAT.Model)
  | ProbMIP (MIP.Problem Scientific) (Trail (Map MIP.Var Rational))

readProblem :: Options -> String -> IO Problem
readProblem o fname = do
  enc <- T.mapM mkTextEncoding (optFileEncoding o)
  let mipOpt = def{ MIP.optFileEncoding = enc, MIP.optMPSWriteObjName = optMPSObjName o }
  
  case FF.getBaseExtension fname of
    ".cnf"
      | optAsMaxSAT o -> do
          prob <- FF.readFile fname
          case maxsat2wbo prob of
            (prob', info) -> return $ ProbWBO prob' (Trail info)
      | otherwise -> do
          prob <- FF.readFile fname
          case sat2pb prob of
            (prob', info) -> return $ ProbOPB  prob' (Trail info)
    ".wcnf" -> do
      prob <- FF.readFile fname
      case maxsat2wbo prob of
        (prob', info) -> return $ ProbWBO prob' (Trail info)
    ".opb"  -> do
      prob <-
        if optPBFastParser o then
          liftM FF.unWithFastParser $ FF.readFile fname
        else
          FF.readFile fname
      return $ ProbOPB prob (Trail IdentityTransformer)
    ".wbo"  -> do
      prob <-
        if optPBFastParser o then
          liftM FF.unWithFastParser $ FF.readFile fname
        else
          FF.readFile fname
      return $ ProbWBO prob (Trail IdentityTransformer)
    ".gcnf" -> do
      prob <- FF.readFile fname
      case gcnf2maxsat prob of
        (prob1, info1) ->
          case maxsat2wbo prob1 of
            (prob2, info2) ->
              return $ ProbWBO prob2 (Trail (ComposedTransformer info1 info2))
    ".lp"   -> do
      prob <- MIP.readLPFile mipOpt fname
      return $ ProbMIP prob (Trail IdentityTransformer)
    ".mps"  -> do
      prob <- MIP.readMPSFile mipOpt fname
      return $ ProbMIP prob (Trail IdentityTransformer)
    ".qubo" -> do
      (qubo :: QUBO.Problem Scientific) <- FF.readFile fname
      case qubo2pb qubo of
        (prob', info) ->
          return $ ProbOPB prob' (Trail info)
    ext ->
      error $ "unknown file extension: " ++ show ext

transformProblem :: Options -> Problem -> Problem
transformProblem o = transformObj o . transformPBLinearization o . transformMIPRemoveUserCuts o

transformObj :: Options -> Problem -> Problem
transformObj o problem =
  case problem of
    ProbOPB opb info | isNothing (PBFile.pbObjectiveFunction opb) -> ProbOPB (setObj (optObjType o) opb) info
    _ -> problem

transformPBLinearization :: Options -> Problem -> Problem
transformPBLinearization o problem
  | optLinearization o =
      case problem of
        ProbOPB opb (Trail info) ->
          case linearizePB  opb (optLinearizationUsingPB o) of
            (opb', info') -> ProbOPB opb' (Trail (ComposedTransformer info info'))
        ProbWBO wbo (Trail info) ->
          case linearizeWBO wbo (optLinearizationUsingPB o) of
            (wbo', info') -> ProbWBO wbo' (Trail (ComposedTransformer info info'))
        ProbMIP mip info -> ProbMIP mip info
  | otherwise = problem

transformMIPRemoveUserCuts :: Options -> Problem -> Problem
transformMIPRemoveUserCuts o problem
  | optRemoveUserCuts o =
      case problem of
        ProbMIP mip info -> ProbMIP (mip{ MIP.userCuts = [] }) info
        _ -> problem
  | otherwise = problem

transformKSat :: Options -> (CNF.CNF, Trail SAT.Model) -> (CNF.CNF, Trail SAT.Model)
transformKSat o (cnf, Trail info) =
  case optKSat o of
    Nothing -> (cnf, Trail info)
    Just k ->
      case sat2ksat k cnf of
        (cnf2, info2) -> (cnf2, Trail (ComposedTransformer info info2))

transformPB2SAT :: Options -> (PBFile.Formula, Trail SAT.Model) -> (CNF.CNF, Trail SAT.Model)
transformPB2SAT o (opb, Trail info) =
  case pb2satWith (optPBEncoding o) opb of
    (cnf, info') -> (cnf, Trail (ComposedTransformer info info'))

transformWBO2MaxSAT :: Options -> (PBFile.SoftFormula, Trail SAT.Model) -> (CNF.WCNF, Trail SAT.Model)
transformWBO2MaxSAT o (wbo, Trail info) =
  case wbo2maxsatWith (optPBEncoding o) wbo of
    (wcnf, info') -> (wcnf, Trail (ComposedTransformer info info'))

transformNormalizeOPB :: (PBFile.Formula, Trail SAT.Model) -> (PBFile.Formula, Trail SAT.Model)
transformNormalizeOPB (opb, Trail info) =
  case normalizePB opb of
    (opb', info') -> (opb', Trail (ComposedTransformer info info'))

transformPB2QUBO :: (PBFile.Formula, Trail SAT.Model) -> ((QUBO.Problem Integer, Integer), Trail QUBO.Solution)
transformPB2QUBO (opb, Trail info) =
  case pb2qubo opb of
    ((qubo, th), info') -> ((qubo, th), Trail (ComposedTransformer info info'))

transformNormalizeMIP :: (MIP.Problem Scientific, Trail (Map MIP.Var Rational)) -> (MIP.Problem Scientific, Trail (Map MIP.Var Rational))
transformNormalizeMIP (ip, Trail info) =
  case normalizeMIPObjective ip of
    (ip', info') -> (ip', Trail (ComposedTransformer info info'))

writeProblem :: Options -> Problem -> IO ()
writeProblem o problem = do
  enc <- T.mapM mkTextEncoding (optFileEncoding o)
  let mipOpt = def{ MIP.optFileEncoding = enc, MIP.optMPSWriteObjName = optMPSObjName o }

  let mip2smtOpt =
        def
        { MIP2SMT.optSetLogic     = optSMTSetLogic o
        , MIP2SMT.optCheckSAT     = not (optSMTNoCheck o)
        , MIP2SMT.optProduceModel = not (optSMTNoProduceModel o)
        , MIP2SMT.optOptimize     = optSMTOptimize o
        }

      writeInfo :: (Transformer a, J.ToJSON a) => a -> IO ()
      writeInfo info =
        case optInfoOutput o of
          Just fname -> J.encodeFile fname info
          Nothing -> return ()

      writeInfo' :: Trail a -> IO ()
      writeInfo' (Trail info) = writeInfo info

  case optOutput o of
    Nothing -> do
      hSetBinaryMode stdout True
      hSetBuffering stdout (BlockBuffering Nothing)
      case problem of
        ProbOPB opb (Trail info) -> do
          ByteStringBuilder.hPutBuilder stdout $ FF.render opb
          writeInfo info
        ProbWBO wbo (Trail info) -> do
          ByteStringBuilder.hPutBuilder stdout $ FF.render wbo
          writeInfo info
        ProbMIP mip (Trail info) -> do
          case MIP.toLPString def mip of
            Left err -> hPutStrLn stderr ("conversion failure: " ++ err) >> exitFailure
            Right s -> do
              F.mapM_ (hSetEncoding stdout) enc
              TLIO.hPutStr stdout s
              writeInfo info

    Just fname -> do
      let opbAndTrail =
            case problem of
              ProbOPB opb info -> (opb, info)
              ProbWBO wbo (Trail info) ->
                case wbo2pb wbo of
                  (opb, info')
                    | optLinearization o ->
                        -- WBO->OPB conversion may have introduced non-linearity
                        case linearizePB opb (optLinearizationUsingPB o) of
                          (opb', info'') -> (opb', Trail (ComposedTransformer info (ComposedTransformer info' info'')))
                    | otherwise -> (opb, Trail (ComposedTransformer info info'))
              ProbMIP mip (Trail info) ->
                case ip2pb (fmap toRational mip) of
                  Left err -> error err
                  Right (opb, info') -> (opb, Trail (ComposedTransformer info info'))
          wboAndTrail =
            case problem of
              ProbOPB opb (Trail info) ->
                case pb2wbo opb of
                  (wbo, info') -> (wbo, Trail (ComposedTransformer info info'))
              ProbWBO wbo info -> (wbo, info)
              ProbMIP _   _ ->
                case (pb2wbo (fst opbAndTrail), snd opbAndTrail) of
                    ((wbo, info'), Trail info) -> (wbo, Trail (ComposedTransformer info info'))
          mipAndTrail =
            case problem of
               ProbOPB opb (Trail info) ->
                 case pb2ip opb of
                   (ip, info') -> (fmap fromInteger ip, Trail (ComposedTransformer info info'))
               ProbWBO wbo (Trail info) ->
                 case wbo2ip (optIndicatorConstraint o) wbo of
                   (ip, info') -> (fmap fromInteger ip, Trail (ComposedTransformer info info'))
               ProbMIP mip info -> (mip, info)
          lsp =
            case problem of
              ProbOPB opb _ -> pb2lsp opb
              ProbWBO wbo _ -> wbo2lsp wbo
              ProbMIP _ _   -> pb2lsp (fst opbAndTrail)
      case FF.getBaseExtension fname of
        ".opb" -> do
          case transformNormalizeOPB opbAndTrail of
            (opb, trail) -> do
              FF.writeFile fname opb
              writeInfo' trail
        ".wbo" -> do
          FF.writeFile fname $ normalizeWBO (fst wboAndTrail)
          writeInfo' (snd wboAndTrail)
        ".cnf" ->
          case transformKSat o $ transformPB2SAT o opbAndTrail of
            (cnf, Trail info) -> do
              FF.writeFile fname cnf
              writeInfo info
        ".wcnf" ->
          case transformWBO2MaxSAT o wboAndTrail of
            (wcnf, Trail info) -> do
              if optNewWCNF o then do
                let nwcnf = CNF.NewWCNF [(if w >= CNF.wcnfTopCost wcnf then Nothing else Just w, c) | (w, c) <- CNF.wcnfClauses wcnf]
                FF.writeFile fname nwcnf
              else do
                FF.writeFile fname wcnf
              writeInfo info
        ".lsp" -> do
          withBinaryFile fname WriteMode $ \h ->
            ByteStringBuilder.hPutBuilder h lsp
          case optInfoOutput o of
            Just _ -> error "--dump-info is not supported for LSP output"
            Nothing -> return ()
        ".lp" -> do
          case transformNormalizeMIP mipAndTrail of
             (mip, Trail info) -> do
               MIP.writeLPFile mipOpt fname mip
               writeInfo info
        ".mps" -> do
          case transformNormalizeMIP mipAndTrail of
             (mip, Trail info) -> do
               MIP.writeMPSFile mipOpt fname mip
               writeInfo info
        ".smp" -> do
          withBinaryFile fname WriteMode $ \h ->
            ByteStringBuilder.hPutBuilder h (pb2smp False (fst opbAndTrail))
          writeInfo' (snd opbAndTrail)
        ".smt2" -> do
          withFile fname WriteMode $ \h -> do
            F.mapM_ (hSetEncoding h) enc
            TLIO.hPutStr h $ TextBuilder.toLazyText $
              MIP2SMT.mip2smt mip2smtOpt (fmap toRational (fst mipAndTrail))
          writeInfo' (snd mipAndTrail)
        ".ys" -> do
          let lang = MIP2SMT.YICES (if optYices2 o then MIP2SMT.Yices2 else MIP2SMT.Yices1)
          withFile fname WriteMode $ \h -> do
            F.mapM_ (hSetEncoding h) enc
            TLIO.hPutStr h $ TextBuilder.toLazyText $
              MIP2SMT.mip2smt mip2smtOpt{ MIP2SMT.optLanguage = lang } (fmap toRational (fst mipAndTrail))
          writeInfo' (snd mipAndTrail)
        ".qubo" ->
          case transformPB2QUBO opbAndTrail of
            ((qubo, _th), Trail info) -> do
              FF.writeFile fname (fmap (fromInteger :: Integer -> Scientific) qubo)
              writeInfo info
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
