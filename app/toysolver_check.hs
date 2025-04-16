{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Control.Monad
import Data.Array.IArray
import Data.Char
import Data.Default.Class
import Data.IORef
import Data.List (sortBy)
import Data.Ord
import qualified Data.PseudoBoolean as PBFile
import Data.String
import qualified Data.Version as V
import qualified Numeric.Optimization.MIP as MIP
import Options.Applicative hiding (Const)
import System.Environment
import System.Exit
import System.FilePath
import System.IO
import Text.Printf

import qualified ToySolver.FileFormat as FF
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.SAT.Types as SAT
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
  } deriving (Eq, Show)

optionsParser :: Parser Options
optionsParser = Options
  <$> fileInput
  <*> solutionFileInput
  <*> modeOption
  <*> fileEncodingOption
  <*> pbFastParserOption
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

  errorRef <- newIORef False

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

  case mode of
    ModeSAT -> do
      (cnf :: CNF.CNF) <- FF.readFile (optInputFile opt)
      return ()

    ModePB -> do
      opb <-
        if optPBFastParser opt then
          liftM FF.unWithFastParser $ FF.readFile (optInputFile opt)
        else
          FF.readFile (optInputFile opt)
      model <- liftM parsePBLog (readFile (optSolutionFile opt))

      case PBFile.pbObjectiveFunction opb of
        Nothing -> return ()
        Just obj -> putStrLn $ "objective value = " ++ show (SAT.evalPBSum model obj)
      forM_ (PBFile.pbConstraints opb) $ \constr -> do
        unless (SAT.evalPBConstraint model constr) $ do
          printf "violated: %s\n" (showPBConstraint constr :: String)
          writeIORef errorRef True

    ModeWBO -> do
      wbo <-
        if optPBFastParser opt then
          liftM FF.unWithFastParser $ FF.readFile (optInputFile opt)
        else
          FF.readFile (optInputFile opt)
      model <- liftM parsePBLog (readFile (optSolutionFile opt))

      obj <- fmap sum $ forM (PBFile.wboConstraints wbo) $ \(w, constr) -> do
        if SAT.evalPBConstraint model constr then
          return 0
        else do
          case w of
            Nothing -> do
              printf "violated: %s\n" (showPBConstraint constr :: String)
              writeIORef errorRef True
              return 0
            Just w' -> do
              return w'
      putStrLn $ "objective value = " ++ show obj

      case PBFile.wboTopCost wbo of
        Just top | top <= obj -> do
          printf "objective value is greater than or equal to top cost (%d)\n" top
          writeIORef errorRef True
        _ -> return ()
      
      return ()

    ModeMaxSAT -> do
      (wcnf :: CNF.WCNF)  <- FF.readFile (optInputFile opt)
      return ()

    ModeMIP -> do
      enc <- mapM mkTextEncoding $ optFileEncoding opt
      mip <- MIP.readFile def{ MIP.optFileEncoding = enc } (optInputFile opt)
      return ()

  errored <- readIORef errorRef
  when errored $ exitFailure

getExt :: String -> String
getExt name | (base, ext) <- splitExtension name =
  case map toLower ext of
#ifdef WITH_ZLIB
    ".gz" -> getExt base
#endif
    s -> s

showPBSum :: (Monoid a, IsString a) => PBFile.Sum -> a
showPBSum = mconcat . map showWeightedTerm
  where
    showWeightedTerm :: (Monoid a, IsString a) => PBFile.WeightedTerm -> a
    showWeightedTerm (c, lits) = foldr (\f g -> f <> fromString " " <> g) mempty (x:xs)
      where
        x = if c >= 0 then fromString "+" <> fromString (show c) else fromString (show c)
        xs = map showLit $ sortBy (comparing abs) lits

    showLit :: (Monoid a, IsString a) => PBFile.Lit -> a
    showLit lit = if lit > 0 then v else fromString "~" <> v
      where
        v = fromString "x" <> fromString (show (abs lit))

showPBConstraint :: (Monoid a, IsString a) => PBFile.Constraint -> a
showPBConstraint (lhs, op, rhs) =
  showPBSum lhs <> f op <>  fromString " " <> fromString (show rhs) <> fromString ";\n"
  where
    f PBFile.Eq = fromString "="
    f PBFile.Ge = fromString ">="

parsePBLog :: String -> SAT.Model
parsePBLog s = array (1, maximum (0 : map fst ls2)) ls2
  where
    ls = lines s
    ls2 = do
      l <- ls
      case l of
        'v':xs -> do
          w <- words xs
          case w of
            '-':'x':ys -> return (read ys, False)
            'x':ys -> return (read ys, True)
        _ -> mzero
