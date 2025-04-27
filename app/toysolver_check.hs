{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Control.Monad
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.Char
import Data.Default.Class
import Data.Scientific
import qualified Data.Version as V
import qualified Numeric.Optimization.MIP as MIP
import qualified Numeric.Optimization.MIP.Solution.Gurobi as GurobiSol
import Options.Applicative hiding (Const)
import System.Exit
import System.FilePath
import System.IO

import qualified ToySolver.FileFormat as FF
import ToySolver.Internal.SolutionChecker
import ToySolver.SAT.LogParser (parseSATLog, parseMaxSATLog, parsePBLog)
import ToySolver.Internal.Util (setEncodingChar8)
import ToySolver.Version


data Mode = ModeSAT | ModePB | ModeWBO | ModeMaxSAT | ModeMIP
  deriving (Eq, Ord, Show)

data Options = Options
  { optInputFile :: FilePath
  , optSolutionFile :: FilePath
  , optMode :: Maybe Mode
  , optFileEncoding :: Maybe String
  , optPBFastParser :: Bool
  , optMIPTol :: MIP.Tol Scientific
  }

optionsParser :: Parser Options
optionsParser = Options
  <$> fileInput
  <*> solutionFileInput
  <*> modeOption
  <*> fileEncodingOption
  <*> pbFastParserOption
  <*> mipTolOptions
  where
    fileInput :: Parser FilePath
    fileInput = argument str (metavar "FILE")

    solutionFileInput :: Parser FilePath
    solutionFileInput = argument str (metavar "SOLUTION_FILE")

    modeOption :: Parser (Maybe Mode)
    modeOption = optional $
          flag' ModeSAT    (long "sat"    <> help "load boolean satisfiability problem in .cnf file")
      <|> flag' ModePB     (long "pb"     <> help "load pseudo boolean problem in .opb file")
      <|> flag' ModeWBO    (long "wbo"    <> help "load weighted boolean optimization problem in .wbo file")
      <|> flag' ModeMaxSAT (long "maxsat" <> help "load MaxSAT problem in .cnf or .wcnf file")
      <|> flag' ModeMIP    (long "lp"     <> help "load LP/MIP problem in .lp or .mps file")

    fileEncodingOption :: Parser (Maybe String)
    fileEncodingOption = optional $ strOption
      $  long "encoding"
      <> metavar "ENCODING"
      <> help "file encoding for LP/MPS files"

    pbFastParserOption :: Parser Bool
    pbFastParserOption = switch
      $  long "pb-fast-parser"
      <> help "use attoparsec-based parser instead of megaparsec-based one for speed"

    mipTolOptions :: Parser (MIP.Tol Scientific)
    mipTolOptions = MIP.Tol <$> intTol <*> feasTol <*> optTol
      where
        intTol = option auto
          $  long "tol-integrality"
          <> metavar "REAL"
          <> help "If a value of integer variable is within this amount from its nearest integer, it is considered feasible."
          <> value (MIP.integralityTol def)
          <> showDefault
        feasTol = option auto
          $  long "tol-feasibility"
          <> metavar "REAL"
          <> help "If the amount of violation of constraints is within this amount, it is considered feasible."
          <> value (MIP.feasibilityTol def)
          <> showDefault
        optTol = option auto
          $  long "tol-optimality"
          <> metavar "REAL"
          <> help "Feasiblity tolerance of dual constraints."
          <> value (MIP.optimalityTol def)
          <> showDefault

parserInfo :: ParserInfo Options
parserInfo = info (helper <*> versionOption <*> optionsParser)
  $  fullDesc
  <> header "toysolver-check - a solution checker"
  where
    versionOption :: Parser (a -> a)
    versionOption = infoOption (V.showVersion version)
      $  hidden
      <> long "version"
      <> help "Show version"

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif

  opt <- execParser parserInfo
  let mode =
        case optMode opt of
          Just m  -> m
          Nothing ->
            case getExt (optInputFile opt) of
              ".cnf"  -> ModeSAT
              ".opb"  -> ModePB
              ".wbo"  -> ModeWBO
              ".wcnf" -> ModeMaxSAT
              ".lp"   -> ModeMIP
              ".mps"  -> ModeMIP
              _ -> ModeSAT

  (ok, ls) <- case mode of
    ModeSAT -> do
      cnf  <- FF.readFile (optInputFile opt)
      (status, m) <- liftM parseSATLog (BL.readFile (optSolutionFile opt))
      pure $ checkSATResult cnf (status, m)

    ModePB -> do
      opb <-
        if optPBFastParser opt then
          liftM FF.unWithFastParser $ FF.readFile (optInputFile opt)
        else
          FF.readFile (optInputFile opt)
      (status, o, m) <- liftM parsePBLog (BL.readFile (optSolutionFile opt))
      pure $ checkPBResult opb (status, o, m)

    ModeWBO -> do
      wbo <-
        if optPBFastParser opt then
          liftM FF.unWithFastParser $ FF.readFile (optInputFile opt)
        else
          FF.readFile (optInputFile opt)
      (status, o, m) <- liftM parsePBLog (BL.readFile (optSolutionFile opt))
      pure $ checkWBOResult wbo (status, o, m)

    ModeMaxSAT -> do
      wcnf  <- FF.readFile (optInputFile opt)
      (status, o, m) <- liftM parseMaxSATLog (BL.readFile (optSolutionFile opt))
      pure $ checkMaxSATResult wcnf (status, o, m)

    ModeMIP -> do
      enc <- mapM mkTextEncoding $ optFileEncoding opt
      mip <- MIP.readFile def{ MIP.optFileEncoding = enc } (optInputFile opt)
      sol <- GurobiSol.readFile (optSolutionFile opt)
      let tol = optMIPTol opt
      pure $ checkMIPResult tol mip sol

  mapM_ putStrLn ls

  unless ok $ exitFailure

getExt :: String -> String
getExt name | (base, ext) <- splitExtension name =
  case map toLower ext of
#ifdef WITH_ZLIB
    ".gz" -> getExt base
#endif
    s -> s
