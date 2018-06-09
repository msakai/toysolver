{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  toysat
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (ScopedTypeVariables, CPP)
--
-- A toy-level SAT solver based on CDCL.
--
-----------------------------------------------------------------------------

module Main where

import Control.Applicative ((<$>))
import Control.Concurrent (getNumCapabilities)
import Control.Concurrent.Timeout
import Control.Monad
import Control.Exception
import Data.Array.IArray
import Data.Array.IO
import qualified Data.ByteString.Lazy as BS
import Data.Default.Class
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Foldable as F
import qualified Data.Traversable as T
import Data.Char
import Data.IORef
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Ord
import qualified Data.Vector.Unboxed as V
import Data.Version
import Data.Scientific as Scientific
import Data.Time
import Options.Applicative hiding (info)
import qualified Options.Applicative
import System.IO
import System.Exit
#if !MIN_VERSION_time(1,5,0)
import System.Locale (defaultTimeLocale)
#endif
import System.Clock
import System.FilePath
import qualified System.Info as SysInfo
import qualified System.Random.MWC as Rand
import Text.Printf
#ifdef __GLASGOW_HASKELL__
import GHC.Environment (getFullArgs)
#endif
#if defined(__GLASGOW_HASKELL__)
import qualified GHC.Stats as Stats
#endif

import qualified Data.PseudoBoolean as PBFile
import qualified Data.PseudoBoolean.Attoparsec as PBFileAttoparsec
import qualified ToySolver.Data.MIP as MIP
import qualified ToySolver.Data.MIP.Solution.Gurobi as GurobiSol
import ToySolver.Converter.Base
import ToySolver.Converter.GCNF2MaxSAT
import qualified ToySolver.Converter.MIP2PB as MIP2PB
import ToySolver.Converter.PB
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.PBO as PBO
import qualified ToySolver.SAT.Encoder.Integer as Integer
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.SAT.Encoder.PBNLC as PBNLC
import qualified ToySolver.SAT.MessagePassing.SurveyPropagation as SP
import qualified ToySolver.SAT.MUS as MUS
import qualified ToySolver.SAT.MUS.Enum as MUSEnum
import ToySolver.SAT.Printer
import qualified ToySolver.Text.CNF as CNF
import ToySolver.Version
import ToySolver.Internal.Util (showRational, setEncodingChar8)

import qualified UBCSAT

-- ------------------------------------------------------------------------

data Mode = ModeSAT | ModeMUS | ModeAllMUS | ModePB | ModeWBO | ModeMaxSAT | ModeMIP
  deriving (Eq, Ord, Enum, Bounded)

data Options
  = Options
  { optInput         :: String
  , optMode          :: Maybe Mode
  , optSATConfig     :: SAT.Config
  , optRandomSeed    :: Maybe Rand.Seed
  , optLinearizerPB  :: Bool
  , optOptMethod     :: PBO.Method
  , optObjFunVarsHeuristics :: Bool
  , optLocalSearchInitial   :: Bool
  , optMUSMethod :: MUS.Method
  , optAllMUSMethod :: MUSEnum.Method
  , optPrintRational :: Bool
  , optTimeout :: Integer
  , optWriteFile :: Maybe FilePath
  , optUBCSAT :: FilePath
  , optInitSP :: Bool
  , optTempDir :: Maybe FilePath
  , optFileEncoding :: Maybe String
  }

instance Default Options where
  def =
    Options
    { optInput         = "" -- XXX
    , optMode          = Nothing
    , optSATConfig     = def
    , optRandomSeed    = Nothing
    , optLinearizerPB  = False
    , optOptMethod     = def
    , optObjFunVarsHeuristics = PBO.defaultEnableObjFunVarsHeuristics
    , optLocalSearchInitial   = False
    , optMUSMethod = MUS.optMethod def
    , optAllMUSMethod = MUSEnum.optMethod def
    , optPrintRational = False
    , optTimeout = 0
    , optWriteFile = Nothing
    , optUBCSAT = "ubcsat"
    , optInitSP = False
    , optTempDir = Nothing
    , optFileEncoding = Nothing
    }

optionsParser :: Parser Options
optionsParser = Options
  <$> fileInput
  <*> modeOption
  <*> satConfigParser
  <*> randomSeedOption
  <*> linearizerPBOption
  <*> optMethodOption
  <*> objFunVarsHeuristicsOption
  <*> localSearchInitialOption
  <*> musMethodOption
  <*> allMUSMethodOption
  <*> printRationalOption
  <*> timeoutOption
  <*> writeFileOption
  <*> ubcsatOption
  <*> initSPOption
  <*> tempDirOption
  <*> fileEncodingOption
  where
    fileInput :: Parser String
    fileInput = strArgument $ metavar "(FILE|-)"

    modeOption :: Parser (Maybe Mode)
    -- modeOption = liftA msum $ T.sequenceA $ map optional $
    modeOption = optional $ foldr (<|>) empty
      [ flag' ModeSAT    $ long "sat"     <> help "solve boolean satisfiability problem in .cnf file"
      , flag' ModeMUS    $ long "mus"     <> help "solve minimally unsatisfiable subset problem in .gcnf or .cnf file"
      , flag' ModeAllMUS $ long "all-mus" <> help "enumerate minimally unsatisfiable subset of .gcnf or .cnf file"
      , flag' ModePB     $ long "pb"      <> help "solve pseudo boolean problem in .opb file"
      , flag' ModeWBO    $ long "wbo"     <> help "solve weighted boolean optimization problem in .wbo file"
      , flag' ModeMaxSAT $ long "maxsat"  <> help "solve MaxSAT problem in .cnf or .wcnf file"
      , flag' ModeMIP    $ long "lp"      <> help "solve LP/MIP problem in .lp or .mps file"
      ]

    randomSeedOption = optional $ fmap (Rand.toSeed . V.fromList . map read . words) $ strOption
      $  long "random-seed"
      <> long "random-gen"
      <> metavar "\"INT ..\""
      <> help "random seed used by the random variable selection"

    linearizerPBOption = switch
      $  long "linearizer-pb"
      <> help "Use PB constraint in linearization."

    optMethodOption = option (maybeReader PBO.parseMethod)
      $  long "opt-method"
      <> metavar "STR"
      <> help ("Optimization method: " ++ intercalate ", " [PBO.showMethod m | m <- [minBound..maxBound]])
      <> value (optOptMethod def)
      <> showDefaultWith PBO.showMethod

    objFunVarsHeuristicsOption =
          flag' True
            (  long "objfun-heuristics"
            <> help ("Enable heuristics for polarity/activity of variables in objective function" ++
                     (if PBO.defaultEnableObjFunVarsHeuristics then " (default)" else "")))
      <|> flag' False
            (  long "no-objfun-heuristics"
            <> help ("Disable heuristics for polarity/activity of variables in objective function" ++
                     (if PBO.defaultEnableObjFunVarsHeuristics then "" else " (default)")))
      <|> pure PBO.defaultEnableObjFunVarsHeuristics

    localSearchInitialOption = switch
      $  long "ls-initial"
      <> help "Use local search (currently UBCSAT) for finding initial solution"

    musMethodOption = option (maybeReader MUS.parseMethod)
      $  long "mus-method"
      <> metavar "STR"
      <> help ("MUS computation method: " ++ intercalate ", " [MUS.showMethod m | m <- [minBound..maxBound]])
      <> value (optMUSMethod def)
      <> showDefaultWith MUS.showMethod

    allMUSMethodOption = option (maybeReader MUSEnum.parseMethod)
      $  long "all-mus-method"
      <> metavar "STR"
      <> help (("MUS enumeration method: " ++ intercalate ", " [MUSEnum.showMethod m | m <- [minBound..maxBound]]))
      <> value (optAllMUSMethod def)
      <> showDefaultWith MUSEnum.showMethod

    printRationalOption = switch
      $  long "print-rational"
      <> help "print rational numbers instead of decimals"

    timeoutOption = option auto
      $  long "timeout"
      <> metavar "INT"
      <> help "Kill toysat after given number of seconds (0 means no limit)"
      <> value (optTimeout def)
      <> showDefault

    writeFileOption = optional $ strOption
      $  short 'w'
      <> metavar "FILE"
      <> help "write model to filename in Gurobi .sol format"

    ubcsatOption = strOption
      $  long "with-ubcsat"
      <> metavar "PATH"
      <> help "give the path to the UBCSAT command"
      <> value (optUBCSAT def)

    initSPOption = switch
      $  long "init-sp"
      <> help "Use survey propation to compute initial polarity (when possible)"

    tempDirOption = optional $ strOption
      $  long "temp-dir"
      <> metavar "PATH"
      <> help "temporary directory"

    fileEncodingOption = optional $ strOption
      $  long "encoding"
      <> metavar "ENCODING"
      <> help "file encoding for LP/MPS files"


satConfigParser :: Parser SAT.Config
satConfigParser = SAT.Config
  <$> restartOption
  <*> restartFirstOption
  <*> restartIncOption
  <*> learningOption
  <*> learntSizeFirstOption
  <*> learntSizeIncOption
  <*> ccMinOption
  <*> branchOption
  <*> eRWAStepSizeFirstOption
  <*> eRWAStepSizeDecOption
  <*> eRWAStepSizeMinOption
  <*> eMADecayOption
  <*> enablePhaseSavingOption
  <*> enableForwardSubsumptionRemovalOption
  <*> enableBackwardSubsumptionRemovalOption
  <*> randomFreqOption
  <*> pbHandlerTypeOption
  <*> enablePBSplitClausePartOption
  <*> checkModelOption
  <*> pure (SAT.configVarDecay def)
  <*> pure (SAT.configConstrDecay def)
  where
    restartOption = option (maybeReader SAT.parseRestartStrategy)
      $  long "restart"
      <> metavar "STR"
      <> help ("Restart startegy: " ++ intercalate ", " [SAT.showRestartStrategy s | s <- [minBound..maxBound]])
      <> value (SAT.configRestartStrategy def)
      <> showDefaultWith SAT.showRestartStrategy
    restartFirstOption = option auto
      $  long "restart-first"
      <> metavar "INT"
      <> help "The initial restart limit."
      <> value (SAT.configRestartFirst def)
      <> showDefault
    restartIncOption = option auto
      $  long "restart-inc"
      <> metavar "REAL"
      <> help "The factor with which the restart limit is multiplied in each restart."
      <> value (SAT.configRestartInc def)
      <> showDefault

    learningOption = option (maybeReader SAT.parseLearningStrategy)
      $  long "learning"
      <> metavar "STR"
      <> help ("Leaning scheme: " ++ intercalate ", " [SAT.showLearningStrategy s | s <- [minBound..maxBound]])
      <> value (SAT.configLearningStrategy def)
      <> showDefaultWith SAT.showLearningStrategy
    learntSizeFirstOption = option auto
      $  long "learnt-size-first"
      <> metavar "INT"
      <> help "The initial limit for learnt clauses."
      <> value (SAT.configLearntSizeFirst def)
      <> showDefault
    learntSizeIncOption = option auto
      $  long "learnt-size-inc"
      <> metavar "REAL"
      <> help "The limit for learnt clauses is multiplied with this factor periodically."
      <> value (SAT.configLearntSizeInc def)
      <> showDefault

    ccMinOption = option auto
      $  long "ccmin"
      <> metavar "INT"
      <> help "Conflict clause minimization: 0=none, 1=local, 2=recursive"
      <> value (SAT.configCCMin def)
      <> showDefault
    branchOption = option (maybeReader SAT.parseBranchingStrategy)
      $  long "branch"
      <> metavar "STR"
      <> help ("Branching startegy: " ++ intercalate ", " [SAT.showBranchingStrategy s | s <- [minBound..maxBound]])
      <> value (SAT.configBranchingStrategy def)
      <> showDefaultWith SAT.showBranchingStrategy

    eRWAStepSizeFirstOption = option auto
      $  long "erwa-alpha-first"
      <> metavar "REAL"
      <> help "step-size alpha in ERWA and LRB branching heuristic is initialized with this value."
      <> value (SAT.configERWAStepSizeFirst def)
      <> showDefault
    eRWAStepSizeDecOption = option auto
      $  long "erwa-alpha-dec"
      <> metavar "REAL"
      <> help "step-size alpha in ERWA and LRB branching heuristic is decreased by this value after each conflict."
      <> value (SAT.configERWAStepSizeDec def)
      <> showDefault
    eRWAStepSizeMinOption = option auto
      $  long "erwa-alpha-min"
      <> metavar "REAL"
      <> help "step-size alpha in ERWA and LRB branching heuristic is decreased until it reach the value."
      <> value (SAT.configERWAStepSizeMin def)
      <> showDefault

    eMADecayOption = option auto
      $  long "ema-decay"
      <> metavar "REAL"
      <> help "inverse of the variable EMA decay factor used by LRB branching heuristic."
      <> value (SAT.configEMADecay def)
      <> showDefault

    enablePhaseSavingOption =
          flag' True  (long "enable-phase-saving"  <> help ("Enable phase saving"  ++ (if SAT.configEnablePhaseSaving def then " (default)" else "")))
      <|> flag' False (long "disable-phase-saving" <> help ("Disable phase saving" ++ (if SAT.configEnablePhaseSaving def then "" else " (default)")))
      <|> pure (SAT.configEnablePhaseSaving def)

    enableForwardSubsumptionRemovalOption =
          flag' True
            (  long "enable-forward-subsumption-removal"
            <> help ("Enable forward subumption removal (clauses only)"  ++ (if SAT.configEnableForwardSubsumptionRemoval def then " (default)" else "")))
      <|> flag' False
            (  long "disable-forward-subsumption-removal"
            <> help ("Disable forward subumption removal (clauses only)" ++ (if SAT.configEnableForwardSubsumptionRemoval def then "" else " (default)")))
      <|> pure (SAT.configEnableForwardSubsumptionRemoval def)
    enableBackwardSubsumptionRemovalOption =
          flag' True
            (  long "enable-backward-subsumption-removal"
            <> help ("Enable backward subumption removal (clauses only)"  ++ (if SAT.configEnableBackwardSubsumptionRemoval def then " (default)" else "")))
      <|> flag' False
            (  long "disable-backward-subsumption-removal"
            <> help ("Disable backward subumption removal (clauses only)" ++ (if SAT.configEnableBackwardSubsumptionRemoval def then "" else " (default)")))
      <|> pure (SAT.configEnableBackwardSubsumptionRemoval def)

    randomFreqOption = option auto
      $  long "random-freq"
      <> metavar "0..1"
      <> help "The frequency with which the decision heuristic tries to choose a random variable"
      <> value (SAT.configRandomFreq def)
      <> showDefault

    pbHandlerTypeOption = option (maybeReader SAT.parsePBHandlerType)
      $  long "pb-handler"
      <> metavar "STR"
      <> help ("PB constraint handler: " ++ intercalate ", " [SAT.showPBHandlerType h | h <- [minBound..maxBound]])
      <> value (SAT.configPBHandlerType def)
      <> showDefaultWith SAT.showPBHandlerType

    enablePBSplitClausePartOption =
          flag' True
            (  long "pb-split-clause-part"
            <> help ("Split clause part of PB constraints." ++ (if SAT.configEnablePBSplitClausePart def then " (default)" else "")))
      <|> flag' False
            (  long "no-pb-split-clause-part"
            <> help ("Do not split clause part of PB constraints." ++ (if SAT.configEnablePBSplitClausePart def then "" else " (default)")))
      <|> pure (SAT.configEnablePBSplitClausePart def)

    checkModelOption = switch
      $  long "check-model"
      <> help "check model for debugging"

parserInfo :: ParserInfo Options
parserInfo = Options.Applicative.info (helper <*> versionOption <*> optionsParser)
  $  fullDesc
  <> header "toysat - a solver for SAT-related problems"
  where
    versionOption :: Parser (a -> a)
    versionOption = infoOption (showVersion version)
      $  hidden
      <> long "version"
      <> help "Show version"

#if !MIN_VERSION_optparse_applicative(0,13,0)

-- | Convert a function producing a 'Maybe' into a reader.
maybeReader :: (String -> Maybe a) -> ReadM a
maybeReader f = eitherReader $ \arg ->
  case f arg of
    Nothing -> Left $ "cannot parse value `" ++ arg ++ "'"
    Just a -> Right a

#endif

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif

  startCPU <- getTime ProcessCPUTime
  startWC  <- getTime Monotonic

  opt <- execParser parserInfo
  let mode =
        case optMode opt of
          Just m  -> m
          Nothing ->
            case map toLower (takeExtension (optInput opt)) of
              ".cnf"  -> ModeSAT
              ".gcnf" -> ModeMUS
              ".opb"  -> ModePB
              ".wbo"  -> ModeWBO
              ".wcnf" -> ModeMaxSAT
              ".lp"   -> ModeMIP
              ".mps"  -> ModeMIP
              _ -> ModeSAT

  printSysInfo
#ifdef __GLASGOW_HASKELL__
  fullArgs <- getFullArgs
#else
  let fullArgs = args
#endif
  putCommentLine $ printf "command line = %s" (show fullArgs)

  let timelim = optTimeout opt * 10^(6::Int)
  
  ret <- timeout (if timelim > 0 then timelim else (-1)) $ do
     solver <- newSolver opt
     case mode of
       ModeSAT     -> mainSAT opt solver
       ModeMUS     -> mainMUS opt solver
       ModeAllMUS  -> mainMUS opt solver
       ModePB      -> mainPB opt solver
       ModeWBO     -> mainWBO opt solver
       ModeMaxSAT  -> mainMaxSAT opt solver
       ModeMIP     -> mainMIP opt solver

  when (isNothing ret) $ do
    putCommentLine "TIMEOUT"
  endCPU <- getTime ProcessCPUTime
  endWC  <- getTime Monotonic
  putCommentLine $ printf "total CPU time = %.3fs" (durationSecs startCPU endCPU)
  putCommentLine $ printf "total wall clock time = %.3fs" (durationSecs startWC endWC)
  printGCStat

printGCStat :: IO ()
#if defined(__GLASGOW_HASKELL__)
#if __GLASGOW_HASKELL__ >= 802
printGCStat = do
  b <- Stats.getRTSStatsEnabled
  when b $ do
    stat <- Stats.getRTSStats
    putCommentLine "RTSStats:"
    putCommentLine $ printf "  gcs = %d"                             $ Stats.gcs stat
    putCommentLine $ printf "  major_gcs = %d"                       $ Stats.major_gcs stat
    putCommentLine $ printf "  allocated_bytes = %d"                 $ Stats.allocated_bytes stat
    putCommentLine $ printf "  max_live_bytes = %d"                  $ Stats.max_live_bytes stat
    putCommentLine $ printf "  max_large_objects_bytes = %d"         $ Stats.max_large_objects_bytes stat
    putCommentLine $ printf "  max_compact_bytes = %d"               $ Stats.max_compact_bytes stat
    putCommentLine $ printf "  max_slop_bytes = %d"                  $ Stats.max_slop_bytes stat
    putCommentLine $ printf "  max_mem_in_use_bytes = %d"            $ Stats.max_mem_in_use_bytes stat
    putCommentLine $ printf "  cumulative_live_bytes = %d"           $ Stats.cumulative_live_bytes stat
    putCommentLine $ printf "  copied_bytes = %d"                    $ Stats.copied_bytes stat
    putCommentLine $ printf "  par_copied_bytes = %d"                $ Stats.par_copied_bytes stat
    putCommentLine $ printf "  cumulative_par_max_copied_bytes = %d" $ Stats.cumulative_par_max_copied_bytes stat
    putCommentLine $ printf "  mutator_cpu_ns = %d"                  $ Stats.mutator_cpu_ns stat
    putCommentLine $ printf "  mutator_elapsed_ns = %d"              $ Stats.mutator_elapsed_ns stat
    putCommentLine $ printf "  gc_cpu_ns = %d"                       $ Stats.gc_cpu_ns stat
    putCommentLine $ printf "  gc_elapsed_ns = %d"                   $ Stats.gc_elapsed_ns stat
    putCommentLine $ printf "  cpu_ns = %d"                          $ Stats.cpu_ns stat
    putCommentLine $ printf "  elapsed_ns = %d"                      $ Stats.elapsed_ns stat
    let gc = Stats.gc stat
    putCommentLine $ "  gc:"
    putCommentLine $ printf "    gen = %d"                           $ Stats.gcdetails_gen gc
    putCommentLine $ printf "    threads = %d"                       $ Stats.gcdetails_threads gc
    putCommentLine $ printf "    allocated_bytes = %d"               $ Stats.gcdetails_allocated_bytes gc
    putCommentLine $ printf "    live_bytes = %d"                    $ Stats.gcdetails_live_bytes gc
    putCommentLine $ printf "    large_objects_bytes = %d"           $ Stats.gcdetails_large_objects_bytes gc
    putCommentLine $ printf "    compact_bytes = %d"                 $ Stats.gcdetails_compact_bytes gc
    putCommentLine $ printf "    slop_bytes = %d"                    $ Stats.gcdetails_slop_bytes gc
    putCommentLine $ printf "    mem_in_use_bytes = %d"              $ Stats.gcdetails_mem_in_use_bytes gc
    putCommentLine $ printf "    copied_bytes = %d"                  $ Stats.gcdetails_copied_bytes gc
    putCommentLine $ printf "    par_max_copied_bytes = %d"          $ Stats.gcdetails_par_max_copied_bytes gc
    putCommentLine $ printf "    sync_elapsed_ns = %d"               $ Stats.gcdetails_sync_elapsed_ns gc
    putCommentLine $ printf "    cpu_ns = %d"                        $ Stats.gcdetails_cpu_ns gc
    putCommentLine $ printf "    elapsed_ns = %d"                    $ Stats.gcdetails_elapsed_ns gc
#else
printGCStat = do
  b <- Stats.getGCStatsEnabled
  when b $ do
    stat <- Stats.getGCStats
    putCommentLine "GCStats:"
    putCommentLine $ printf "  bytesAllocated = %d"         $ Stats.bytesAllocated stat
    putCommentLine $ printf "  numGcs = %d"                 $ Stats.numGcs stat
    putCommentLine $ printf "  maxBytesUsed = %d"           $ Stats.maxBytesUsed stat
    putCommentLine $ printf "  numByteUsageSamples = %d"    $ Stats.numByteUsageSamples stat
    putCommentLine $ printf "  cumulativeBytesUsed = %d"    $ Stats.cumulativeBytesUsed stat
    putCommentLine $ printf "  bytesCopied = %d"            $ Stats.bytesCopied stat
    putCommentLine $ printf "  currentBytesUsed = %d"       $ Stats.currentBytesUsed stat
    putCommentLine $ printf "  currentBytesSlop = %d"       $ Stats.currentBytesSlop stat
    putCommentLine $ printf "  maxBytesSlop = %d"           $ Stats.maxBytesSlop stat
    putCommentLine $ printf "  peakMegabytesAllocated = %d" $ Stats.peakMegabytesAllocated stat
    putCommentLine $ printf "  mutatorCpuSeconds = %5.2f"   $ Stats.mutatorCpuSeconds stat
    putCommentLine $ printf "  mutatorWallSeconds = %5.2f"  $ Stats.mutatorWallSeconds stat
    putCommentLine $ printf "  gcCpuSeconds = %5.2f"        $ Stats.gcCpuSeconds stat
    putCommentLine $ printf "  gcWallSeconds = %5.2f"       $ Stats.gcWallSeconds stat
    putCommentLine $ printf "  cpuSeconds = %5.2f"          $ Stats.cpuSeconds stat
    putCommentLine $ printf "  wallSeconds = %5.2f"         $ Stats.wallSeconds stat
    putCommentLine $ printf "  parTotBytesCopied = %d"      $ Stats.parTotBytesCopied stat
    putCommentLine $ printf "  parMaxBytesCopied = %d"      $ Stats.parMaxBytesCopied stat
#endif
#else
printGCStat = return ()
#endif

printSysInfo :: IO ()
printSysInfo = do
  tm <- getZonedTime
  putCommentLine $ printf "%s" (formatTime defaultTimeLocale "%FT%X%z" tm)
  putCommentLine $ printf "version = %s" (showVersion version)
  putCommentLine $ printf "githash = %s" (fromMaybe "<unknown>" gitHash)
  putCommentLine $ printf "compilationtime = %s" (show compilationTime)
  putCommentLine $ printf "arch = %s" SysInfo.arch
  putCommentLine $ printf "os = %s" SysInfo.os
  putCommentLine $ printf "compiler = %s %s" SysInfo.compilerName (showVersion SysInfo.compilerVersion)
  putCommentLine "packages:"
  forM_ packageVersions $ \(package, ver) -> do
    putCommentLine $ printf "  %s-%s" package ver

putCommentLine :: String -> IO ()
putCommentLine s = do
  putStr "c "
  putStrLn s
  hFlush stdout

putSLine :: String -> IO ()
putSLine  s = do
  putStr "s "
  putStrLn s
  hFlush stdout

putOLine :: String -> IO ()
putOLine  s = do
  putStr "o "
  putStrLn s
  hFlush stdout

newSolver :: Options -> IO SAT.Solver
newSolver opts = do
  solver <- SAT.newSolverWithConfig (optSATConfig opts)
  SAT.setLogger solver putCommentLine
  case optRandomSeed opts of
    Nothing -> SAT.setRandomGen solver =<< Rand.createSystemRandom
    Just s -> SAT.setRandomGen solver =<< Rand.initialize (Rand.fromSeed s)
  do gen <- SAT.getRandomGen solver
     s <- Rand.save gen
     putCommentLine $ "use --random-gen=" ++ show (unwords . map show . V.toList . Rand.fromSeed $ s) ++ " option to reproduce the execution"
  return solver

-- ------------------------------------------------------------------------

mainSAT :: Options -> SAT.Solver -> IO ()
mainSAT opt solver = do
  ret <- case optInput opt of
           "-"   -> liftM CNF.parse $ BS.hGetContents stdin
           fname -> CNF.parseFile fname
  case ret of
    Left err -> hPrint stderr err >> exitFailure
    Right cnf -> do
      let fname = if ".cnf" `isSuffixOf` map toLower (optInput opt)
                  then Just (optInput opt)
                  else Nothing
      solveSAT opt solver cnf fname

solveSAT :: Options -> SAT.Solver -> CNF.CNF -> Maybe FilePath -> IO ()
solveSAT opt solver cnf cnfFileName = do
  putCommentLine $ printf "#vars %d" (CNF.cnfNumVars cnf)
  putCommentLine $ printf "#constraints %d" (CNF.cnfNumClauses cnf)
  SAT.newVars_ solver (CNF.cnfNumVars cnf)
  forM_ (CNF.cnfClauses cnf) $ \clause ->
    SAT.addClause solver (SAT.unpackClause clause)

  spHighlyBiased <-
    if optInitSP opt then do
      initPolarityUsingSP solver (CNF.cnfNumVars cnf)
        (CNF.cnfNumVars cnf) [(1, clause) | clause <- CNF.cnfClauses cnf]
    else
      return IntMap.empty

  when (optLocalSearchInitial opt) $ do
    fixed <- SAT.getFixedLiterals solver
    let var_init1 = IntMap.fromList [(abs lit, lit > 0) | lit <- fixed, abs lit <= CNF.cnfNumVars cnf]
        var_init2 = IntMap.map (>0) spHighlyBiased
        -- note that IntMap.union is left-biased.
        var_init = [if b then v else -v | (v, b) <- IntMap.toList (var_init1 `IntMap.union` var_init2)]
    let wcnf =
          CNF.WCNF
          { CNF.wcnfNumVars = CNF.cnfNumVars cnf
          , CNF.wcnfNumClauses = CNF.cnfNumClauses cnf
          , CNF.wcnfTopCost = 1
          , CNF.wcnfClauses = [(1, clause) | clause <- CNF.cnfClauses cnf]
          }
    let opt2 =
          def
          { UBCSAT.optCommand = optUBCSAT opt
          , UBCSAT.optTempDir = optTempDir opt
          , UBCSAT.optProblem = wcnf
          , UBCSAT.optProblemFile = cnfFileName
          , UBCSAT.optVarInit = var_init
          }
    ret <- UBCSAT.ubcsatBest opt2
    case ret of
      Nothing -> return ()
      Just (_,m) -> do
        forM_ (assocs m) $ \(v, val) -> do
          SAT.setVarPolarity solver v val

  result <- SAT.solve solver
  putSLine $ if result then "SATISFIABLE" else "UNSATISFIABLE"
  when result $ do
    m <- SAT.getModel solver
    satPrintModel stdout m (CNF.cnfNumVars cnf)
    writeSOLFile opt m Nothing (CNF.cnfNumVars cnf)

initPolarityUsingSP :: SAT.Solver -> Int -> Int -> [(Double, SAT.PackedClause)] -> IO (IntMap Double)
initPolarityUsingSP solver nvOrig nv clauses = do
  n <- getNumCapabilities
  putCommentLine $ "Running survey propgation using " ++ show n ++" threads ..."
  startWC  <- getTime Monotonic
  sp <- SP.newSolver nv clauses
  SP.initializeRandom sp =<< SAT.getRandomGen solver
  SP.setNThreads sp n
  lits <- SAT.getFixedLiterals solver
  forM_ lits $ \lit -> do
    when (abs lit <= nvOrig) $ SP.fixLit sp lit
  b <- SP.propagate sp
  endWC  <- getTime Monotonic
  if b then do
    putCommentLine $ printf "Survey propagation converged in %.3fs" (durationSecs startWC endWC)
    xs <- liftM catMaybes $ forM [1 .. nvOrig] $ \v -> do
      (pt,pf,_)<- SP.getVarProb sp v
      let bias = pt - pf
      SAT.setVarPolarity solver v (bias >= 0)
      if abs bias > 0.3 then
        return $ Just (v, bias)
      else
        return Nothing
    forM_ (zip (sortBy (comparing (abs . snd)) xs) [1..]) $ \((v,_),w) -> do
      replicateM w $ SAT.varBumpActivity solver v
    return $ IntMap.fromList xs
  else do
    putCommentLine $ printf "Survey propagation did not converge"
    return $ IntMap.empty

-- ------------------------------------------------------------------------

mainMUS :: Options -> SAT.Solver -> IO ()
mainMUS opt solver = do
  gcnf <- case optInput opt of
           "-"   -> do
             s <- BS.hGetContents stdin
             case CNF.parse s of
               Left err   -> hPutStrLn stderr err >> exitFailure
               Right gcnf -> return gcnf
           fname -> do
             ret <- CNF.parseFile fname
             case ret of
               Left err   -> hPutStrLn stderr err >> exitFailure
               Right gcnf -> return gcnf
  solveMUS opt solver gcnf

solveMUS :: Options -> SAT.Solver -> CNF.GCNF -> IO ()
solveMUS opt solver gcnf = do
  putCommentLine $ printf "#vars %d" (CNF.gcnfNumVars gcnf)
  putCommentLine $ printf "#constraints %d" (CNF.gcnfNumClauses gcnf)
  putCommentLine $ printf "#groups %d" (CNF.gcnfLastGroupIndex gcnf)

  SAT.resizeVarCapacity solver (CNF.gcnfNumVars gcnf + CNF.gcnfLastGroupIndex gcnf)
  SAT.newVars_ solver (CNF.gcnfNumVars gcnf)

  tbl <- forM [1 .. CNF.gcnfLastGroupIndex gcnf] $ \i -> do
    sel <- SAT.newVar solver
    return (i, sel)
  let idx2sel :: Array Int SAT.Var
      idx2sel = array (1, CNF.gcnfLastGroupIndex gcnf) tbl
      selrng  = if null tbl then (0,-1) else (snd $ head tbl, snd $ last tbl)
      sel2idx :: Array SAT.Lit Int
      sel2idx = array selrng [(sel, idx) | (idx, sel) <- tbl]

  (idx2clausesM :: IOArray Int [SAT.PackedClause]) <- newArray (1, CNF.gcnfLastGroupIndex gcnf) []
  forM_ (CNF.gcnfClauses gcnf) $ \(idx, clause) ->
    if idx==0
    then SAT.addClause solver (SAT.unpackClause clause)
    else do
      SAT.addClause solver (- (idx2sel ! idx) : SAT.unpackClause clause)
      cs <- readArray idx2clausesM idx
      writeArray idx2clausesM idx (clause : cs)
  (idx2clauses :: Array Int [SAT.PackedClause]) <- freeze idx2clausesM

  when (optInitSP opt) $ do
    let (wcnf, _) = gcnf2maxsat gcnf
    initPolarityUsingSP solver (CNF.gcnfNumVars gcnf)
      (CNF.wcnfNumVars wcnf) [(fromIntegral w, clause) | (w, clause) <- CNF.wcnfClauses wcnf]
    return ()

  result <- SAT.solveWith solver (map (idx2sel !) [1..CNF.gcnfLastGroupIndex gcnf])
  putSLine $ if result then "SATISFIABLE" else "UNSATISFIABLE"
  if result
    then do
      m <- SAT.getModel solver
      satPrintModel stdout m (CNF.gcnfNumVars gcnf)
      writeSOLFile opt m Nothing (CNF.gcnfNumVars gcnf)
    else do
      if optMode opt /= Just ModeAllMUS
      then do
          let opt2 = def
                     { MUS.optMethod = optMUSMethod opt
                     , MUS.optLogger = putCommentLine
                     , MUS.optShowLit = \lit -> show (sel2idx ! lit)
                     , MUS.optEvalConstr = \m sel ->
                         and [SAT.evalClause m (SAT.unpackClause c) | c <- idx2clauses ! (sel2idx ! sel)]
                     }
          mus <- MUS.findMUSAssumptions solver opt2
          let mus2 = sort $ map (sel2idx !) $ IntSet.toList mus
          musPrintSol stdout mus2
      else do
          musCounter <- newIORef 1
          mcsCounter <- newIORef 1
          let opt2 = def
                     { MUSEnum.optMethod = optAllMUSMethod opt
                     , MUSEnum.optLogger = putCommentLine
                     , MUSEnum.optShowLit = \lit -> show (sel2idx ! lit)
                     , MUSEnum.optEvalConstr = \m sel ->
                         and [SAT.evalClause m (SAT.unpackClause c) | c <- idx2clauses ! (sel2idx ! sel)]
                     , MUSEnum.optOnMCSFound = \mcs -> do
                         i <- readIORef mcsCounter
                         modifyIORef' mcsCounter (+1)
                         let mcs2 = sort $ map (sel2idx !) $ IntSet.toList mcs
                         putCommentLine $ "MCS #" ++ show (i :: Int) ++ ": " ++ intercalate " " (map show mcs2)
                     , MUSEnum.optOnMUSFound = \mus -> do
                         i <- readIORef musCounter
                         modifyIORef' musCounter (+1)
                         putCommentLine $ "MUS #" ++ show (i :: Int)
                         let mus2 = sort $ map (sel2idx !) $ IntSet.toList mus
                         musPrintSol stdout mus2
                     }
          MUSEnum.allMUSAssumptions solver (map snd tbl) opt2
          return ()

-- ------------------------------------------------------------------------

mainPB :: Options -> SAT.Solver -> IO ()
mainPB opt solver = do
  ret <- case optInput opt of
           "-"   -> liftM PBFileAttoparsec.parseOPBByteString $ BS.hGetContents stdin
           fname -> PBFileAttoparsec.parseOPBFile fname
  case ret of
    Left err -> hPutStrLn stderr err >> exitFailure
    Right formula -> solvePB opt solver formula

solvePB :: Options -> SAT.Solver -> PBFile.Formula -> IO ()
solvePB opt solver formula = do
  let nv = PBFile.pbNumVars formula
      nc = PBFile.pbNumConstraints formula
  putCommentLine $ printf "#vars %d" nv
  putCommentLine $ printf "#constraints %d" nc

  SAT.newVars_ solver nv
  enc <- Tseitin.newEncoderWithPBLin solver
  Tseitin.setUsePB enc (optLinearizerPB opt)
  pbnlc <- PBNLC.newEncoder solver enc

  forM_ (PBFile.pbConstraints formula) $ \(lhs, op, rhs) -> do
    case op of
      PBFile.Ge -> PBNLC.addPBNLAtLeast pbnlc lhs rhs
      PBFile.Eq -> PBNLC.addPBNLExactly pbnlc lhs rhs

  spHighlyBiased <- 
    if optInitSP opt then do
      let (cnf, _) = pb2sat formula
      initPolarityUsingSP solver nv (CNF.cnfNumVars cnf) [(1.0, clause) | clause <- CNF.cnfClauses cnf]
    else
      return IntMap.empty

  initialModel <- 
    if optLocalSearchInitial opt then do
      let (wbo,  info1) = pb2wbo formula
          (wcnf, info2) = wbo2maxsat wbo
      fixed <- filter (\lit -> abs lit <= nv) <$> SAT.getFixedLiterals solver
      let var_init1 = IntMap.fromList [(abs lit, lit > 0) | lit <- fixed, abs lit <= nv]
          var_init2 = IntMap.map (>0) spHighlyBiased
          -- note that IntMap.union is left-biased.
          var_init = [if b then v else -v | (v, b) <- IntMap.toList (var_init1 `IntMap.union` var_init2)]
      let opt2 =
            def
            { UBCSAT.optCommand = optUBCSAT opt
            , UBCSAT.optTempDir = optTempDir opt
            , UBCSAT.optProblem = wcnf
            , UBCSAT.optVarInit = var_init
            }
      ret <- UBCSAT.ubcsatBest opt2
      case ret of
        Nothing -> return Nothing
        Just (obj,m) -> do
          let m2 = transformBackward info1 $ transformBackward info2 m
          forM_ (assocs m2) $ \(v, val) -> do
            SAT.setVarPolarity solver v val
          if obj < CNF.wcnfTopCost wcnf then
            return $ Just m2 
          else
            return Nothing
    else
      return Nothing

  case PBFile.pbObjectiveFunction formula of
    Nothing -> do
      result <- SAT.solve solver
      putSLine $ if result then "SATISFIABLE" else "UNSATISFIABLE"
      when result $ do
        m <- SAT.getModel solver
        pbPrintModel stdout m nv
        writeSOLFile opt m Nothing nv

    Just obj' -> do
      obj'' <- PBNLC.linearizePBSumWithPolarity pbnlc Tseitin.polarityNeg obj'

      nv' <- SAT.getNVars solver
      defs <- Tseitin.getDefinitions enc
      let extendModel :: SAT.Model -> SAT.Model
          extendModel m = array (1,nv') (assocs a)
            where
              -- Use BOXED array to tie the knot
              a :: Array SAT.Var Bool
              a = array (1,nv') $ assocs m ++ [(v, Tseitin.evalFormula a phi) | (v,phi) <- defs]

      pbo <- PBO.newOptimizer2 solver obj'' (\m -> SAT.evalPBSum m obj')
      setupOptimizer pbo opt
      PBO.setOnUpdateBestSolution pbo $ \_ val -> putOLine (show val)
      PBO.setOnUpdateLowerBound pbo $ \lb -> do
        putCommentLine $ printf "lower bound updated to %d" lb

      case initialModel of
        Nothing -> return ()
        Just m -> PBO.addSolution pbo (extendModel m)

      finally (PBO.optimize pbo) $ do
        ret <- PBO.getBestSolution pbo
        case ret of
          Nothing -> do
            b <- PBO.isUnsat pbo
            if b
              then putSLine "UNSATISFIABLE"
              else putSLine "UNKNOWN"
          Just (m, val) -> do
            b <- PBO.isOptimum pbo
            if b
              then putSLine "OPTIMUM FOUND"
              else putSLine "SATISFIABLE"
            pbPrintModel stdout m nv
            writeSOLFile opt m (Just val) nv

setupOptimizer :: PBO.Optimizer -> Options -> IO ()
setupOptimizer pbo opt = do
  PBO.setEnableObjFunVarsHeuristics pbo $ optObjFunVarsHeuristics opt
  PBO.setMethod pbo $ optOptMethod opt
  PBO.setLogger pbo putCommentLine

-- ------------------------------------------------------------------------

mainWBO :: Options -> SAT.Solver -> IO ()
mainWBO opt solver = do
  ret <- case optInput opt of
           "-"   -> liftM PBFileAttoparsec.parseWBOByteString $ BS.hGetContents stdin
           fname -> PBFileAttoparsec.parseWBOFile fname
  case ret of
    Left err -> hPutStrLn stderr err >> exitFailure
    Right formula -> solveWBO opt solver False formula

solveWBO :: Options -> SAT.Solver -> Bool -> PBFile.SoftFormula -> IO ()
solveWBO opt solver isMaxSat formula =
  solveWBO' opt solver isMaxSat formula (wbo2maxsat formula) Nothing

solveWBO'
  :: (BackwardTransformer wbo2maxsat_info, Source wbo2maxsat_info ~ SAT.Model, Target wbo2maxsat_info ~ SAT.Model)
  => Options -> SAT.Solver -> Bool -> PBFile.SoftFormula -> (CNF.WCNF, wbo2maxsat_info) -> Maybe FilePath -> IO ()
solveWBO' opt solver isMaxSat formula (wcnf, wbo2maxsat_info) wcnfFileName = do
  let nv = PBFile.wboNumVars formula
      nc = PBFile.wboNumConstraints formula
  putCommentLine $ printf "#vars %d" nv
  putCommentLine $ printf "#constraints %d" nc

  SAT.resizeVarCapacity solver (nv + length [() | (Just _, _) <- PBFile.wboConstraints formula])
  enc <- Tseitin.newEncoderWithPBLin solver
  Tseitin.setUsePB enc (optLinearizerPB opt)
  pbnlc <- PBNLC.newEncoder solver enc
  (obj, defsPB) <- addWBO pbnlc formula
  objLin <- PBNLC.linearizePBSumWithPolarity pbnlc Tseitin.polarityNeg obj

  spHighlyBiased <-
    if optInitSP opt then do
      initPolarityUsingSP solver nv (CNF.wcnfNumVars wcnf) [(fromIntegral w, c) | (w, c) <-  CNF.wcnfClauses wcnf]
    else
      return IntMap.empty

  initialModel <- liftM (fmap (transformBackward wbo2maxsat_info . snd)) $
    if optLocalSearchInitial opt then do
      fixed <- SAT.getFixedLiterals solver
      let var_init1 = IntMap.fromList [(abs lit, lit > 0) | lit <- fixed, abs lit <= nv]
          var_init2 = IntMap.map (>0) spHighlyBiased
          -- note that IntMap.union is left-biased.
          var_init = [if b then v else -v | (v, b) <- IntMap.toList (var_init1 `IntMap.union` var_init2)]
      let opt2 =
            def
            { UBCSAT.optCommand = optUBCSAT opt
            , UBCSAT.optTempDir = optTempDir opt
            , UBCSAT.optProblem = wcnf
            , UBCSAT.optProblemFile = wcnfFileName
            , UBCSAT.optVarInit = var_init
            }
      UBCSAT.ubcsatBestFeasible opt2
    else
      return Nothing

  nv' <- SAT.getNVars solver
  defsTseitin <- Tseitin.getDefinitions enc
  let extendModel :: SAT.Model -> SAT.Model
      extendModel m = array (1,nv') (assocs a)
        where
          -- Use BOXED array to tie the knot
          a :: Array SAT.Var Bool
          a = array (1,nv') $
                assocs m ++
                [(v, Tseitin.evalFormula a phi) | (v, phi) <- defsTseitin] ++
                [(v, SAT.evalPBConstraint a constr) | (v, constr) <- defsPB]

  let softConstrs = [(c, constr) | (Just c, constr) <- PBFile.wboConstraints formula]
                
  pbo <- PBO.newOptimizer2 solver objLin $ \m ->
           sum [if SAT.evalPBConstraint m constr then 0 else w | (w,constr) <- softConstrs]

  setupOptimizer pbo opt
  PBO.setOnUpdateBestSolution pbo $ \_ val -> putOLine (show val)
  PBO.setOnUpdateLowerBound pbo $ \lb -> do
    putCommentLine $ printf "lower bound updated to %d" lb

  case initialModel of
    Nothing -> return ()
    Just m -> PBO.addSolution pbo (extendModel m)

  finally (PBO.optimize pbo) $ do
    ret <- PBO.getBestSolution pbo
    case ret of
      Nothing -> do
        b <- PBO.isUnsat pbo
        if b
          then putSLine "UNSATISFIABLE"
          else putSLine "UNKNOWN"
      Just (m, val) -> do
        b <- PBO.isOptimum pbo
        if b then do
          putSLine "OPTIMUM FOUND"
          if isMaxSat then
            satPrintModel stdout m nv
          else
            pbPrintModel stdout m nv
          writeSOLFile opt m (Just val) nv
        else if not isMaxSat then do
          putSLine "SATISFIABLE"
          pbPrintModel stdout m nv
          writeSOLFile opt m (Just val) nv
        else 
          putSLine "UNKNOWN"

-- ------------------------------------------------------------------------

mainMaxSAT :: Options -> SAT.Solver -> IO ()
mainMaxSAT opt solver = do
  ret <- case optInput opt of
           "-"   -> liftM CNF.parse BS.getContents
           fname -> CNF.parseFile fname
  case ret of
    Left err -> hPutStrLn stderr err >> exitFailure
    Right wcnf -> do
      let fname = if or [s `isSuffixOf` map toLower (optInput opt) | s <- [".cnf", ".wcnf"]]
                  then Just (optInput opt)
                  else Nothing
      solveMaxSAT opt solver wcnf fname

solveMaxSAT :: Options -> SAT.Solver -> CNF.WCNF -> Maybe FilePath -> IO ()
solveMaxSAT opt solver wcnf wcnfFileName =
  solveWBO' opt solver True wbo (wcnf, ReversedTransformer info) wcnfFileName
  where
    (wbo, info) = maxsat2wbo wcnf

-- ------------------------------------------------------------------------

mainMIP :: Options -> SAT.Solver -> IO ()
mainMIP opt solver = do
  mip <-
    case optInput opt of
      fname@"-"   -> do
        F.mapM_ (\s -> hSetEncoding stdin =<< mkTextEncoding s) (optFileEncoding opt)
        s <- hGetContents stdin
        case MIP.parseLPString def fname s of
          Right mip -> return mip
          Left err ->
            case MIP.parseMPSString def fname s of
              Right mip -> return mip
              Left err2 -> do
                hPrint stderr err
                hPrint stderr err2
                exitFailure
      fname -> do
        enc <- T.mapM mkTextEncoding (optFileEncoding opt)
        MIP.readFile def{ MIP.optFileEncoding = enc } fname
  solveMIP opt solver (fmap toRational mip)

solveMIP :: Options -> SAT.Solver -> MIP.Problem Rational -> IO ()
solveMIP opt solver mip = do
  enc <- Tseitin.newEncoderWithPBLin solver
  Tseitin.setUsePB enc (optLinearizerPB opt)
  pbnlc <- PBNLC.newEncoder solver enc
  ret <- MIP2PB.addMIP pbnlc mip
  case ret of
    Left msg -> do
      putCommentLine msg
      putSLine "UNKNOWN"
      exitFailure
    Right (obj, info) -> do
      (linObj, linObjOffset) <- Integer.linearize pbnlc obj

      let transformObjValBackward :: Integer -> Rational
          transformObjValBackward val = MIP2PB.transformObjValBackward info (val + linObjOffset)

          printModel :: Map MIP.Var Integer -> IO ()
          printModel m = do
            forM_ (Map.toList m) $ \(v, val) -> do
              printf "v %s = %d\n" (MIP.fromVar v) val
            hFlush stdout
  
          writeSol :: Map MIP.Var Integer -> Rational -> IO ()
          writeSol m val = do
            case optWriteFile opt of
              Nothing -> return ()
              Just fname -> do
                let sol = MIP.Solution
                          { MIP.solStatus = MIP.StatusUnknown
                          , MIP.solObjectiveValue = Just $ Scientific.fromFloatDigits (fromRational val :: Double)
                          , MIP.solVariables = Map.fromList [(v, fromIntegral val) | (v,val) <- Map.toList m]
                          }
                GurobiSol.writeFile fname sol
  
      pbo <- PBO.newOptimizer solver linObj
      setupOptimizer pbo opt
      PBO.setOnUpdateBestSolution pbo $ \_ val -> do
        putOLine $ showRational (optPrintRational opt) (transformObjValBackward val)
  
      finally (PBO.optimize pbo) $ do
        ret <- PBO.getBestSolution pbo
        case ret of
          Nothing -> do
            b <- PBO.isUnsat pbo
            if b
              then putSLine "UNSATISFIABLE"
              else putSLine "UNKNOWN"
          Just (m,val) -> do
            b <- PBO.isOptimum pbo
            if b
              then putSLine "OPTIMUM FOUND"
              else putSLine "SATISFIABLE"
            let m2   = transformBackward info m
                val2 = transformObjValBackward val
            printModel m2
            writeSol m2 val2

-- ------------------------------------------------------------------------

writeSOLFile :: Options -> SAT.Model -> Maybe Integer -> Int -> IO ()
writeSOLFile opt m obj nbvar = do
  case optWriteFile opt of
    Nothing -> return ()
    Just fname -> do
      let sol = MIP.Solution
                { MIP.solStatus = MIP.StatusUnknown
                , MIP.solObjectiveValue = fmap fromIntegral obj
                , MIP.solVariables = Map.fromList [(MIP.toVar ("x" ++ show x), if b then 1.0 else 0.0) | (x,b) <- assocs m, x <= nbvar]
                }
      GurobiSol.writeFile fname sol

durationSecs :: TimeSpec -> TimeSpec -> Double
durationSecs start end = fromIntegral (toNanoSecs (end `diffTimeSpec` start)) / 10^(9::Int)
