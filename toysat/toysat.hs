{-# LANGUAGE ScopedTypeVariables, CPP #-}
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

import Control.Concurrent (getNumCapabilities)
import Control.Concurrent.Timeout
import Control.Monad
import Control.Exception
import Data.Array.IArray
import qualified Data.ByteString.Lazy as BS
import Data.Default.Class
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Char
import Data.IORef
import Data.List
import Data.Maybe
import Data.Ord
import Data.Ratio
import Data.Word
import qualified Data.Vector.Unboxed as V
import Data.VectorSpace
import Data.Version
import Data.Time
import System.IO
import System.Environment
import System.Exit
#if !MIN_VERSION_time(1,5,0)
import System.Locale (defaultTimeLocale)
#endif
import System.Console.GetOpt
import System.CPUTime
import System.FilePath
import qualified System.Info as SysInfo
import qualified System.Random.MWC as Rand
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS
import Text.Printf
#ifdef __GLASGOW_HASKELL__
import GHC.Environment (getFullArgs)
#endif
#if defined(__GLASGOW_HASKELL__)
import qualified GHC.Stats as Stats
#endif

import qualified Data.PseudoBoolean as PBFile
import qualified Data.PseudoBoolean.Attoparsec as PBFileAttoparsec
import ToySolver.Data.OrdRel
import qualified ToySolver.Data.MIP as MIP
import qualified ToySolver.Converter.GCNF2MaxSAT as GCNF2MaxSAT
import qualified ToySolver.Converter.MaxSAT2WBO as MaxSAT2WBO
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.PBO as PBO
import qualified ToySolver.SAT.Integer as Integer
import qualified ToySolver.SAT.TseitinEncoder as Tseitin
import qualified ToySolver.SAT.PBNLC as PBNLC
import qualified ToySolver.SAT.MessagePassing.SurveyPropagation as SP
import qualified ToySolver.SAT.MUS as MUS
import qualified ToySolver.SAT.MUS.QuickXplain as QuickXplain
import qualified ToySolver.SAT.MUS.CAMUS as CAMUS
import qualified ToySolver.SAT.MUS.DAA as DAA
import ToySolver.SAT.Printer
import qualified ToySolver.Text.MaxSAT as MaxSAT
import qualified ToySolver.Text.GCNF as GCNF
import qualified ToySolver.Text.GurobiSol as GurobiSol
import ToySolver.Version
import ToySolver.Internal.Util (showRational, revForM, setEncodingChar8)

import UBCSAT

-- ------------------------------------------------------------------------

data Mode = ModeHelp | ModeVersion | ModeSAT | ModeMUS | ModePB | ModeWBO | ModeMaxSAT | ModeMIP

data MUSMethod = MUSLinear | MUSQuickXplain

data AllMUSMethod = AllMUSCAMUS | AllMUSDAA

data Options
  = Options
  { optMode          :: Maybe Mode
  , optSATConfig     :: SAT.Config
  , optRandomSeed    :: Maybe Rand.Seed
  , optLinearizerPB  :: Bool
  , optSearchStrategy       :: PBO.SearchStrategy
  , optObjFunVarsHeuristics :: Bool
  , optLocalSearchInitial   :: Bool
  , optMUSMethod :: MUSMethod
  , optAllMUSes :: Bool
  , optAllMUSMethod :: AllMUSMethod
  , optPrintRational :: Bool
  , optTimeout :: Integer
  , optWriteFile :: Maybe FilePath
  , optUBCSAT :: FilePath
  , optInitSP :: Bool
  }

instance Default Options where
  def =
    Options
    { optMode          = Nothing
    , optSATConfig     = def
    , optRandomSeed    = Nothing
    , optLinearizerPB  = False
    , optSearchStrategy       = def
    , optObjFunVarsHeuristics = PBO.defaultEnableObjFunVarsHeuristics
    , optLocalSearchInitial   = False
    , optMUSMethod = MUSLinear
    , optAllMUSes = False
    , optAllMUSMethod = AllMUSCAMUS
    , optPrintRational = False
    , optTimeout = 0
    , optWriteFile = Nothing
    , optUBCSAT = "ubcsat"
    , optInitSP = False
    }

options :: [OptDescr (Options -> Options)]
options =
    [ Option ['h'] ["help"]   (NoArg (\opt -> opt{ optMode = Just ModeHelp   })) "show help"
    , Option [] ["version"]   (NoArg (\opt -> opt{ optMode = Just ModeVersion})) "show version"

    , Option []    ["sat"]    (NoArg (\opt -> opt{ optMode = Just ModeSAT    })) "solve boolean satisfiability problem in .cnf file (default)"
    , Option []    ["mus"]    (NoArg (\opt -> opt{ optMode = Just ModeMUS    })) "solve minimally unsatisfiable subset problem in .gcnf or .cnf file"
    , Option []    ["pb"]     (NoArg (\opt -> opt{ optMode = Just ModePB     })) "solve pseudo boolean problem in .opb file"
    , Option []    ["wbo"]    (NoArg (\opt -> opt{ optMode = Just ModeWBO    })) "solve weighted boolean optimization problem in .wbo file"
    , Option []    ["maxsat"] (NoArg (\opt -> opt{ optMode = Just ModeMaxSAT })) "solve MaxSAT problem in .cnf or .wcnf file"
    , Option []    ["lp"]     (NoArg (\opt -> opt{ optMode = Just ModeMIP    })) "solve bounded integer programming problem in .lp or .mps file"

    , Option [] ["restart"]
        (ReqArg (\val opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configRestartStrategy = parseRestartStrategy val } }) "<str>")
        "Restart startegy: MiniSAT (default), Armin, Luby."
    , Option [] ["restart-first"]
        (ReqArg (\val opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configRestartFirst = read val } }) "<integer>")
        (printf "The initial restart limit. (default %d)" (SAT.configRestartFirst def))
    , Option [] ["restart-inc"]
        (ReqArg (\val opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configRestartInc = read val } }) "<real>")
        (printf "The factor with which the restart limit is multiplied in each restart. (default %f)" (SAT.configRestartInc def))
    , Option [] ["learning"]
        (ReqArg (\val opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configLearningStrategy = parseLS val } }) "<name>")
        "Leaning scheme: clause (default), hybrid"
    , Option [] ["learnt-size-first"]
        (ReqArg (\val opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configLearntSizeFirst = read val } }) "<int>")
        "The initial limit for learnt clauses."
    , Option [] ["learnt-size-inc"]
        (ReqArg (\val opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configLearntSizeInc = read val } }) "<real>")
        (printf "The limit for learnt clauses is multiplied with this factor periodically. (default %f)" (SAT.configLearntSizeInc def))
    , Option [] ["ccmin"]
        (ReqArg (\val opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configCCMin = read val } }) "<int>")
        (printf "Conflict clause minimization (0=none, 1=local, 2=recursive; default %d)" (SAT.configCCMin def))
    , Option [] ["enable-phase-saving"]
        (NoArg (\opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configEnablePhaseSaving = True } }))
        ("Enable phase saving" ++ (if SAT.configEnablePhaseSaving def then " (default)" else ""))
    , Option [] ["disable-phase-saving"]
        (NoArg (\opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configEnablePhaseSaving = False } }))
        ("Disable phase saving" ++ (if SAT.configEnablePhaseSaving def then "" else " (default)"))
    , Option [] ["enable-forward-subsumption-removal"]
        (NoArg (\opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configEnableForwardSubsumptionRemoval = True } }))
        ("Enable forward subumption removal (clauses only)" ++ (if SAT.configEnableForwardSubsumptionRemoval def then " (default)" else ""))
    , Option [] ["disable-forward-subsumption-removal"]
        (NoArg (\opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configEnableForwardSubsumptionRemoval = False } }))
        ("Disable forward subsumption removal (clauses only)" ++ (if SAT.configEnableForwardSubsumptionRemoval def then "" else " (default)"))
    , Option [] ["enable-backward-subsumption-removal"]
        (NoArg (\opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configEnableBackwardSubsumptionRemoval = True } }))
        ("Enable backward subsumption removal." ++ (if SAT.configEnableBackwardSubsumptionRemoval def then " (default)" else ""))
    , Option [] ["disable-backward-subsumption-removal"]
        (NoArg (\opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configEnableBackwardSubsumptionRemoval = False } }))
        ("Disable backward subsumption removal." ++ (if SAT.configEnableBackwardSubsumptionRemoval def then "" else " (default)"))

    , Option [] ["random-freq"]
        (ReqArg (\val opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configRandomFreq = read val } }) "<0..1>")
        (printf "The frequency with which the decision heuristic tries to choose a random variable (default %f)" (SAT.configRandomFreq def))
    , Option [] ["random-seed"]
        (ReqArg (\val opt -> opt{ optRandomSeed = Just (Rand.toSeed (V.singleton (read val) :: V.Vector Word32)) }) "<int>")
        "random seed used by the random variable selection"
    , Option [] ["random-gen"]
        (ReqArg (\val opt -> opt{ optRandomSeed = Just (Rand.toSeed (V.fromList (map read $ words $ val) :: V.Vector Word32)) }) "<str>")
        "another way of specifying random seed used by the random variable selection"

    , Option [] ["init-sp"]
        (NoArg (\opt -> opt{ optInitSP = True }))
        "Use survey propation to compute initial polarity (CNF only)"

    , Option [] ["linearizer-pb"]
        (NoArg (\opt -> opt{ optLinearizerPB = True }))
        "Use PB constraint in linearization."

    , Option [] ["pb-handler"]
        (ReqArg (\val opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configPBHandlerType = parsePBHandler val } }) "<name>")
        "PB constraint handler: counter (default), pueblo"
    , Option [] ["pb-split-clause-part"]
        (NoArg (\opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configEnablePBSplitClausePart = True } }))
        ("Split clause part of PB constraints." ++ (if SAT.configEnablePBSplitClausePart def then " (default)" else ""))
    , Option [] ["no-pb-split-clause-part"]
        (NoArg (\opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configEnablePBSplitClausePart = False } }))
        ("Do not split clause part of PB constraints." ++ (if SAT.configEnablePBSplitClausePart def then "" else " (default)"))

    , Option [] ["search"]
        (ReqArg (\val opt -> opt{ optSearchStrategy = parseSearch val }) "<str>")
        "Search algorithm used in optimization; linear (default), binary, adaptive, unsat, msu4, bc, bcd, bcd2"
    , Option [] ["objfun-heuristics"]
        (NoArg (\opt -> opt{ optObjFunVarsHeuristics = True }))
        "Enable heuristics for polarity/activity of variables in objective function (default)"
    , Option [] ["no-objfun-heuristics"]
        (NoArg (\opt -> opt{ optObjFunVarsHeuristics = False }))
        "Disable heuristics for polarity/activity of variables in objective function"
    , Option [] ["ls-initial"]
        (NoArg (\opt -> opt{ optLocalSearchInitial = True }))
        "Use local search (currently UBCSAT) for finding initial solution"

    , Option [] ["all-mus"]
        (NoArg (\opt -> opt{ optMode = Just ModeMUS, optAllMUSes = True }))
        "enumerate all MUSes"
    , Option [] ["mus-method"]
        (ReqArg (\val opt -> opt{ optMUSMethod = parseMUSMethod val }) "<str>")
        "MUS computation method: linear (default), QuickXplain"
    , Option [] ["all-mus-method"]
        (ReqArg (\val opt -> opt{ optAllMUSMethod = parseAllMUSMethod val }) "<str>")
        "MUS enumeration method: camus (default), daa"

    , Option [] ["print-rational"]
        (NoArg (\opt -> opt{ optPrintRational = True }))
        "print rational numbers instead of decimals"
    , Option ['w'] []
        (ReqArg (\val opt -> opt{ optWriteFile = Just val }) "<filename>")
        "write model to filename in Gurobi .sol format"

    , Option [] ["check-model"]
        (NoArg (\opt -> opt{ optSATConfig = (optSATConfig opt){ SAT.configCheckModel = True } }))
        "check model for debug"

    , Option [] ["timeout"]
        (ReqArg (\val opt -> opt{ optTimeout = read val }) "<int>")
        "Kill toysat after given number of seconds (default 0 (no limit))"

    , Option [] ["with-ubcsat"]
        (ReqArg (\val opt -> opt{ optUBCSAT = val }) "<PATH>")
        "give the path to the UBCSAT command"
    ]
  where
    parseRestartStrategy s =
      case map toLower s of
        "minisat" -> SAT.MiniSATRestarts
        "armin" -> SAT.ArminRestarts
        "luby" -> SAT.LubyRestarts
        _ -> error (printf "unknown restart strategy \"%s\"" s)

    parseSearch s =
      case map toLower s of
        "linear"   -> PBO.LinearSearch
        "binary"   -> PBO.BinarySearch
        "adaptive" -> PBO.AdaptiveSearch
        "unsat"    -> PBO.UnsatBased
        "msu4"     -> PBO.MSU4
        "bc"       -> PBO.BC
        "bcd"      -> PBO.BCD
        "bcd2"     -> PBO.BCD2
        _ -> error (printf "unknown search strategy \"%s\"" s)

    parseMUSMethod s =
      case map toLower s of
        "linear"      -> MUSLinear
        "quickxplain" -> MUSQuickXplain
        _ -> error (printf "unknown MUS finding method \"%s\"" s)

    parseAllMUSMethod s =
      case map toLower s of
        "camus"    -> AllMUSCAMUS
        "daa"      -> AllMUSDAA
        _ -> error (printf "unknown MUS enumeration method \"%s\"" s)

    parseLS s =
      case map toLower s of
        "clause" -> SAT.LearningClause
        "hybrid" -> SAT.LearningHybrid
        _ -> error (printf "unknown learning strategy \"%s\"" s)

    parsePBHandler s =
      case map toLower s of
        "counter" -> SAT.PBHandlerTypeCounter
        "pueblo"  -> SAT.PBHandlerTypePueblo
        _ -> error (printf "unknown PB constraint handler %s" s)

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif

  startCPU <- getCPUTime
  startWC  <- getCurrentTime
  args <- getArgs
  case getOpt Permute options args of
    (_,_,errs@(_:_)) -> do
      mapM_ putStrLn errs
      exitFailure

    (o,args2,[]) -> do
      let opt = foldl (flip id) def o      
          mode =
            case optMode opt of
              Just m  -> m
              Nothing ->
                case args2 of
                  [] -> ModeHelp
                  fname : _ ->
                    case map toLower (takeExtension fname) of
                      ".cnf"  -> ModeSAT
                      ".gcnf" -> ModeMUS
                      ".opb"  -> ModePB
                      ".wbo"  -> ModeWBO
                      ".wcnf" -> ModeMaxSAT
                      ".lp"   -> ModeMIP
                      ".mps"  -> ModeMIP
                      _ -> ModeSAT

      case mode of
        ModeHelp    -> showHelp stdout
        ModeVersion -> hPutStrLn stdout (showVersion version)
        _ -> do
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
               ModeHelp    -> showHelp stdout
               ModeVersion -> hPutStrLn stdout (showVersion version)
               ModeSAT     -> mainSAT opt solver args2
               ModeMUS     -> mainMUS opt solver args2
               ModePB      -> mainPB opt solver args2
               ModeWBO     -> mainWBO opt solver args2
               ModeMaxSAT  -> mainMaxSAT opt solver args2
               ModeMIP     -> mainMIP opt solver args2
    
          when (isNothing ret) $ do
            putCommentLine "TIMEOUT"
          endCPU <- getCPUTime
          endWC  <- getCurrentTime
          putCommentLine $ printf "total CPU time = %.3fs" (fromIntegral (endCPU - startCPU) / 10^(12::Int) :: Double)
          putCommentLine $ printf "total wall clock time = %.3fs" (realToFrac (endWC `diffUTCTime` startWC) :: Double)
          printGCStat

printGCStat :: IO ()
#if defined(__GLASGOW_HASKELL__)
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
#else
printGCStat = return ()
#endif

showHelp :: Handle -> IO ()
showHelp h = hPutStrLn h (usageInfo header options)

header :: String
header = unlines
  [ "Usage:"
  , "  toysat [OPTION]... [file.cnf|-]"
  , "  toysat [OPTION]... --mus [file.gcnf|-]"
  , "  toysat [OPTION]... --pb [file.opb|-]"
  , "  toysat [OPTION]... --wbo [file.wbo|-]"
  , "  toysat [OPTION]... --maxsat [file.cnf|file.wcnf|-]"
  , "  toysat [OPTION]... --lp [file.lp|file.mps|-]"
  , ""
  , "Options:"
  ]

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

mainSAT :: Options -> SAT.Solver -> [String] -> IO ()
mainSAT opt solver args = do
  ret <- case args of
           ["-"]   -> liftM (DIMACS.parseByteString "-") $ BS.hGetContents stdin
           [fname] -> DIMACS.parseFile fname
           _ -> showHelp stderr >> exitFailure
  case ret of
    Left err -> hPrint stderr err >> exitFailure
    Right cnf -> solveSAT opt solver cnf

solveSAT :: Options -> SAT.Solver -> DIMACS.CNF -> IO ()
solveSAT opt solver cnf = do
  putCommentLine $ printf "#vars %d" (DIMACS.numVars cnf)
  putCommentLine $ printf "#constraints %d" (DIMACS.numClauses cnf)
  SAT.newVars_ solver (DIMACS.numVars cnf)
  forM_ (DIMACS.clauses cnf) $ \clause ->
    SAT.addClause solver (elems clause)
  when (optInitSP opt) $
    initPolarityUsingSP solver (DIMACS.numVars cnf)
      (DIMACS.numVars cnf) [(1, elems clause) | clause <- DIMACS.clauses cnf]
  result <- SAT.solve solver
  putSLine $ if result then "SATISFIABLE" else "UNSATISFIABLE"
  when result $ do
    m <- SAT.getModel solver
    satPrintModel stdout m (DIMACS.numVars cnf)
    writeSOLFile opt m Nothing (DIMACS.numVars cnf)

initPolarityUsingSP :: SAT.Solver -> Int -> Int -> [(Double, SAT.Clause)] -> IO ()
initPolarityUsingSP solver nvOrig nv clauses = do
  n <- getNumCapabilities
  putCommentLine $ "Running survey propgation using " ++ show n ++" threads ..."
  startWC  <- getCurrentTime
  sp <- SP.newSolver nv clauses  
  SP.initializeRandom sp =<< SAT.getRandomGen solver
  SP.setNThreads sp n
  lits <- SAT.getFixedLiterals solver
  forM_ lits $ \lit -> do
    when (abs lit <= nvOrig) $ SP.fixLit sp lit
  b <- SP.propagate sp
  endWC  <- getCurrentTime
  if b then do
    putCommentLine $ printf "Survey propagation converged in %.3fs" (realToFrac (endWC `diffUTCTime` startWC) :: Double)
    xs <- forM [1 .. nvOrig] $ \v -> do
      (pt,pf,_)<- SP.getVarProb sp v
      let bias = pt - pf
      SAT.setVarPolarity solver v (bias >= 0)
      if abs bias > 0.1 then
        return $ Just (v, abs bias)
      else
        return Nothing
    forM_ (sortBy (comparing snd) (catMaybes xs)) $ \(v,_) -> do
      SAT.varBumpActivity solver v
  else do
    putCommentLine $ printf "Survey propagation did not converge"
    return ()

-- ------------------------------------------------------------------------

mainMUS :: Options -> SAT.Solver -> [String] -> IO ()
mainMUS opt solver args = do
  gcnf <- case args of
           ["-"]   -> do
             s <- hGetContents stdin
             case GCNF.parseString s of
               Left err   -> hPutStrLn stderr err >> exitFailure
               Right gcnf -> return gcnf
           [fname] -> do
             ret <- GCNF.parseFile fname
             case ret of
               Left err   -> hPutStrLn stderr err >> exitFailure
               Right gcnf -> return gcnf
           _ -> showHelp stderr >> exitFailure
  solveMUS opt solver gcnf

solveMUS :: Options -> SAT.Solver -> GCNF.GCNF -> IO ()
solveMUS opt solver gcnf = do
  putCommentLine $ printf "#vars %d" (GCNF.numVars gcnf)
  putCommentLine $ printf "#constraints %d" (GCNF.numClauses gcnf)
  putCommentLine $ printf "#groups %d" (GCNF.lastGroupIndex gcnf)

  SAT.resizeVarCapacity solver (GCNF.numVars gcnf + GCNF.lastGroupIndex gcnf)
  SAT.newVars_ solver (GCNF.numVars gcnf)

  tbl <- forM [1 .. GCNF.lastGroupIndex gcnf] $ \i -> do
    sel <- SAT.newVar solver
    return (i, sel)
  let idx2sel :: Array Int SAT.Var
      idx2sel = array (1, GCNF.lastGroupIndex gcnf) tbl
      selrng  = if null tbl then (0,-1) else (snd $ head tbl, snd $ last tbl)
      sel2idx :: Array SAT.Lit Int
      sel2idx = array selrng [(sel, idx) | (idx, sel) <- tbl]

  forM_ (GCNF.clauses gcnf) $ \(idx, clause) ->
    if idx==0
    then SAT.addClause solver clause
    else SAT.addClause solver (- (idx2sel ! idx) : clause)

  when (optInitSP opt) $ do
    let wcnf = GCNF2MaxSAT.convert gcnf
    initPolarityUsingSP solver (GCNF.numVars gcnf)
      (MaxSAT.numVars wcnf) [(fromIntegral w, clause) | (w, clause) <- MaxSAT.clauses wcnf]

  result <- SAT.solveWith solver (map (idx2sel !) [1..GCNF.lastGroupIndex gcnf])
  putSLine $ if result then "SATISFIABLE" else "UNSATISFIABLE"
  if result
    then do
      m <- SAT.getModel solver
      satPrintModel stdout m (GCNF.numVars gcnf)
      writeSOLFile opt m Nothing (GCNF.numVars gcnf)
    else do
      if not (optAllMUSes opt)
      then do
          let opt2 = def
                     { MUS.optLogger = putCommentLine
                     , MUS.optLitPrinter = \lit ->
                         show (sel2idx ! lit)
                     }
          mus <-
            case optMUSMethod opt of
              MUSLinear -> MUS.findMUSAssumptions solver opt2
              MUSQuickXplain -> QuickXplain.findMUSAssumptions solver opt2
          let mus2 = sort $ map (sel2idx !) $ IntSet.toList mus
          musPrintSol stdout mus2
      else do
          counter <- newIORef 1
          let opt2 = def
                     { CAMUS.optLogger = putCommentLine
                     , CAMUS.optOnMCSFound = \mcs -> do
                         let mcs2 = sort $ map (sel2idx !) $ IntSet.toList mcs
                         putCommentLine $ "MCS found: " ++ show mcs2
                     , CAMUS.optOnMUSFound = \mus -> do
                         i <- readIORef counter
                         modifyIORef' counter (+1)
                         putCommentLine $ "MUS #" ++ show (i :: Int)
                         let mus2 = sort $ map (sel2idx !) $ IntSet.toList mus
                         musPrintSol stdout mus2
                     }
          case optAllMUSMethod opt of
            AllMUSCAMUS -> CAMUS.allMUSAssumptions solver (map snd tbl) opt2
            AllMUSDAA   -> DAA.allMUSAssumptions solver (map snd tbl) opt2
          return ()

-- ------------------------------------------------------------------------

mainPB :: Options -> SAT.Solver -> [String] -> IO ()
mainPB opt solver args = do
  ret <- case args of
           ["-"]   -> liftM PBFileAttoparsec.parseOPBByteString $ BS.hGetContents stdin
           [fname] -> PBFileAttoparsec.parseOPBFile fname
           _ -> showHelp stderr >> exitFailure
  case ret of
    Left err -> hPutStrLn stderr err >> exitFailure
    Right formula -> solvePB opt solver formula Nothing

solvePB :: Options -> SAT.Solver -> PBFile.Formula -> Maybe SAT.Model -> IO ()
solvePB opt solver formula initialModel = do
  let nv = PBFile.pbNumVars formula
      nc = PBFile.pbNumConstraints formula
  putCommentLine $ printf "#vars %d" nv
  putCommentLine $ printf "#constraints %d" nc

  SAT.newVars_ solver nv
  enc <- Tseitin.newEncoder solver
  Tseitin.setUsePB enc (optLinearizerPB opt)
  pbnlc <- PBNLC.newEncoder solver enc

  forM_ (PBFile.pbConstraints formula) $ \(lhs, op, rhs) -> do
    case op of
      PBFile.Ge -> PBNLC.addPBNLAtLeast pbnlc lhs rhs
      PBFile.Eq -> PBNLC.addPBNLExactly pbnlc lhs rhs

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

      pbo <- PBO.newOptimizer2 solver obj'' (\m -> evalPBSum m obj')
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

evalPBSum :: SAT.IModel m => m -> PBFile.Sum -> Integer
evalPBSum m s = sum [if and [SAT.evalLit m lit | lit <- tm] then c else 0 | (c,tm) <- s]

evalPBConstraint :: SAT.IModel m => m -> PBFile.Constraint -> Bool
evalPBConstraint m (lhs,op,rhs) = op' lhs' rhs
  where
    op' = case op of
            PBFile.Ge -> (>=)
            PBFile.Eq -> (==)
    lhs' = evalPBSum m lhs

setupOptimizer :: PBO.Optimizer -> Options -> IO ()
setupOptimizer pbo opt = do
  PBO.setEnableObjFunVarsHeuristics pbo $ optObjFunVarsHeuristics opt
  PBO.setSearchStrategy pbo $ optSearchStrategy opt
  PBO.setLogger pbo putCommentLine

-- ------------------------------------------------------------------------

mainWBO :: Options -> SAT.Solver -> [String] -> IO ()
mainWBO opt solver args = do
  ret <- case args of
           ["-"]   -> liftM PBFileAttoparsec.parseWBOByteString $ BS.hGetContents stdin
           [fname] -> PBFileAttoparsec.parseWBOFile fname
           _ -> showHelp stderr >> exitFailure
  case ret of
    Left err -> hPutStrLn stderr err >> exitFailure
    Right formula -> solveWBO opt solver False formula Nothing

solveWBO :: Options -> SAT.Solver -> Bool -> PBFile.SoftFormula -> Maybe SAT.Model -> IO ()
solveWBO opt solver isMaxSat formula initialModel = do
  let nv = PBFile.wboNumVars formula
      nc = PBFile.wboNumConstraints formula
  putCommentLine $ printf "#vars %d" nv
  putCommentLine $ printf "#constraints %d" nc

  SAT.resizeVarCapacity solver (nv + length [() | (Just _, _) <- PBFile.wboConstraints formula])
  SAT.newVars_ solver nv
  enc <- Tseitin.newEncoder solver
  Tseitin.setUsePB enc (optLinearizerPB opt)
  pbnlc <- PBNLC.newEncoder solver enc

  objRef <- newIORef []
  defsRef <- newIORef []

  forM_ (PBFile.wboConstraints formula) $ \(cost, constr@(lhs, op, rhs)) -> do
    case cost of
      Nothing -> do
        case op of
          PBFile.Ge -> PBNLC.addPBNLAtLeast pbnlc lhs rhs
          PBFile.Eq -> PBNLC.addPBNLExactly pbnlc lhs rhs
      Just cval -> do
        sel <-
          case op of
            PBFile.Ge -> do
              case lhs of
                [(1,ls)] | rhs == 1 ->
                  Tseitin.encodeConjWithPolarity enc Tseitin.polarityPos ls
                _ -> do
                  sel <- SAT.newVar solver
                  PBNLC.addPBNLAtLeastSoft pbnlc sel lhs rhs
                  modifyIORef defsRef ((sel, constr) : )
                  return sel
            PBFile.Eq -> do
              sel <- SAT.newVar solver
              PBNLC.addPBNLExactlySoft pbnlc sel lhs rhs
              modifyIORef defsRef ((sel, constr) : )
              return sel
        modifyIORef objRef ((cval, SAT.litNot sel) : )

  obj <- readIORef objRef

  case PBFile.wboTopCost formula of
    Nothing -> return ()
    Just c -> SAT.addPBAtMost solver obj (c-1)

  when (optInitSP opt) $ do
    case wboToMaxSAT formula of
      Nothing -> return ()
      Just wcnf -> initPolarityUsingSP solver nv nv [(fromIntegral w, c) | (w, c) <-  MaxSAT.clauses wcnf]

  nv' <- SAT.getNVars solver
  defs1 <- Tseitin.getDefinitions enc
  defs2 <- readIORef defsRef
  let extendModel :: SAT.Model -> SAT.Model
      extendModel m = array (1,nv') (assocs a)
        where
          -- Use BOXED array to tie the knot
          a :: Array SAT.Var Bool
          a = array (1,nv') $
                assocs m ++
                [(v, Tseitin.evalFormula a phi) | (v, phi) <- defs1] ++
                [(v, evalPBConstraint a constr) | (v, constr) <- defs2]

  let softConstrs = [(c, constr) | (Just c, constr) <- PBFile.wboConstraints formula]
                
  pbo <- PBO.newOptimizer2 solver obj $ \m ->
           sum [if evalPBConstraint m constr then 0 else w | (w,constr) <- softConstrs]

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

-- NOTE: This does not encode proper pseudo boolean constraints into clauses,
-- and it also ignores top cost.
wboToMaxSAT :: PBFile.SoftFormula -> Maybe MaxSAT.WCNF
wboToMaxSAT formula = do
  cs <- mapM f (PBFile.wboConstraints formula)
  return $
    MaxSAT.WCNF
    { MaxSAT.numVars    = PBFile.wboNumVars formula
    , MaxSAT.numClauses = PBFile.wboNumConstraints formula
    , MaxSAT.topCost    = w2
    , MaxSAT.clauses    = cs
    }         
  where
    w2 = sum [w | (Just w, _) <- PBFile.wboConstraints formula] + 1
    
    f :: PBFile.SoftConstraint -> Maybe MaxSAT.WeightedClause
    f (w, (cs, PBFile.Ge, 1)) = do
      lits <- forM cs $ \(a,xs) -> do
        guard $ a == 1
        case xs of
          [lit] -> return lit
          _ -> Nothing
      return (case w of{ Just n -> n; Nothing -> w2 }, lits)
    f _ = Nothing

-- ------------------------------------------------------------------------

mainMaxSAT :: Options -> SAT.Solver -> [String] -> IO ()
mainMaxSAT opt solver args = do
  ret <- case args of
           ["-"]   -> liftM MaxSAT.parseByteString BS.getContents
           [fname] -> MaxSAT.parseFile fname
           _ -> showHelp stderr  >> exitFailure
  case ret of
    Left err -> hPutStrLn stderr err >> exitFailure
    Right wcnf -> do
      initialModel <-
        case args of
          [fname] | optLocalSearchInitial opt && or [s `isSuffixOf` map toLower fname | s <- [".cnf", ".wcnf"] ] ->
            UBCSAT.ubcsat (optUBCSAT opt) fname wcnf
          _ -> return Nothing
      solveMaxSAT opt solver wcnf initialModel

solveMaxSAT :: Options -> SAT.Solver -> MaxSAT.WCNF -> Maybe SAT.Model -> IO ()
solveMaxSAT opt solver wcnf initialModel =
  solveWBO opt solver True (MaxSAT2WBO.convert wcnf) initialModel

-- ------------------------------------------------------------------------

mainMIP :: Options -> SAT.Solver -> [String] -> IO ()
mainMIP opt solver args = do
  mip <-
    case args of
      [fname@"-"]   -> do
        s <- hGetContents stdin
        case MIP.parseLPString fname s of
          Right mip -> return mip
          Left err ->
            case MIP.parseMPSString fname s of
              Right mip -> return mip
              Left err2 -> do
                hPrint stderr err
                hPrint stderr err2
                exitFailure
      [fname] -> do
        ret <- MIP.readFile fname
        case ret of
          Left err -> hPrint stderr err >> exitFailure
          Right mip -> return mip
      _ -> showHelp stderr >> exitFailure
  solveMIP opt solver mip

solveMIP :: Options -> SAT.Solver -> MIP.Problem -> IO ()
solveMIP opt solver mip = do
  if not (Set.null nivs) then do
    putCommentLine $ "cannot handle non-integer variables: " ++ intercalate ", " (map MIP.fromVar (Set.toList nivs))
    putSLine "UNKNOWN"
    exitFailure
  else do
    enc <- Tseitin.newEncoder solver
    Tseitin.setUsePB enc (optLinearizerPB opt)
    pbnlc <- PBNLC.newEncoder solver enc

    putCommentLine $ "Loading variables and bounds"
    vmap <- liftM Map.fromList $ revForM (Set.toList ivs) $ \v -> do
      case MIP.getBounds mip v of
        (MIP.Finite lb, MIP.Finite ub) -> do
          v2 <- Integer.newVar pbnlc (ceiling lb) (floor ub)
          return (v,v2)
        _ -> do
          putCommentLine $ "cannot handle unbounded variable: " ++ MIP.fromVar v
          putSLine "UNKNOWN"
          exitFailure

    putCommentLine "Loading constraints"
    forM_ (MIP.constraints mip) $ \c -> do
      let lhs = MIP.constrExpr c                            
      let f op rhs = do
            let d = foldl' lcm 1 (map denominator  (rhs:[r | MIP.Term r _ <- MIP.terms lhs]))
                lhs' = sumV [asInteger (r * fromIntegral d) *^ product [vmap Map.! v | v <- vs] | MIP.Term r vs <- MIP.terms lhs]
                rhs' = asInteger (rhs * fromIntegral d)
                c2 = case op of
                       MIP.Le  -> lhs' .<=. fromInteger rhs'
                       MIP.Ge  -> lhs' .>=. fromInteger rhs'
                       MIP.Eql -> lhs' .==. fromInteger rhs'
            case MIP.constrIndicator c of
              Nothing -> Integer.addConstraint pbnlc c2
              Just (var, val) -> do
                let var' = asBin (vmap Map.! var)
                case val of
                  1 -> Integer.addConstraintSoft pbnlc var' c2
                  0 -> Integer.addConstraintSoft pbnlc (SAT.litNot var') c2
                  _ -> return ()
      case (MIP.constrLB c, MIP.constrUB c) of
        (MIP.Finite x1, MIP.Finite x2) | x1==x2 -> f MIP.Eql x2
        (lb, ub) -> do
          case lb of
            MIP.NegInf -> return ()
            MIP.Finite x -> f MIP.Ge x
            MIP.PosInf -> SAT.addClause solver []
          case ub of
            MIP.NegInf -> SAT.addClause solver []
            MIP.Finite x -> f MIP.Le x
            MIP.PosInf -> return ()

    putCommentLine "Loading SOS constraints"
    forM_ (MIP.sosConstraints mip) $ \MIP.SOSConstraint{ MIP.sosType = typ, MIP.sosBody = xs } -> do
      case typ of
        MIP.S1 -> SAT.addAtMost solver (map (asBin . (vmap Map.!) . fst) xs) 1
        MIP.S2 -> do
          let ps = nonAdjacentPairs $ map fst $ sortBy (comparing snd) $ xs
          forM_ ps $ \(x1,x2) -> do
            SAT.addClause solver [SAT.litNot $ asBin $ vmap Map.! v | v <- [x1,x2]]

    let obj = MIP.objectiveFunction mip
        d = foldl' lcm 1 [denominator r | MIP.Term r _ <- MIP.terms (MIP.objExpr obj)] *
            (if MIP.objDir obj == MIP.OptMin then 1 else -1)
        obj2 = sumV [asInteger (r * fromIntegral d) *^ product [vmap Map.! v | v <- vs] | MIP.Term r vs <- MIP.terms (MIP.objExpr obj)]
    (obj3,obj3_c) <- Integer.linearize pbnlc obj2

    let transformObjVal :: Integer -> Rational
        transformObjVal val = fromIntegral (val + obj3_c) / fromIntegral d

        transformModel :: SAT.Model -> Map String Integer
        transformModel m = Map.fromList
          [ (MIP.fromVar v, Integer.eval m (vmap Map.! v)) | v <- Set.toList ivs ]

        printModel :: Map String Integer -> IO ()
        printModel m = do
          forM_ (Map.toList m) $ \(v, val) -> do
            printf "v %s = %d\n" v val
          hFlush stdout

        writeSol :: Map String Integer -> Rational -> IO ()
        writeSol m val = do
          case optWriteFile opt of
            Nothing -> return ()
            Just fname -> do
              writeFile fname (GurobiSol.render (fmap fromInteger m) (Just (fromRational val)))

    pbo <- PBO.newOptimizer solver obj3
    setupOptimizer pbo opt
    PBO.setOnUpdateBestSolution pbo $ \_ val -> do
      putOLine $ showRational (optPrintRational opt) (transformObjVal val)

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
          let m2   = transformModel m
              val2 = transformObjVal val
          printModel m2
          writeSol m2 val2

  where
    ivs = MIP.integerVariables mip
    nivs = MIP.variables mip `Set.difference` ivs

    asInteger :: Rational -> Integer
    asInteger r
      | denominator r /= 1 = error (show r ++ " is not integer")
      | otherwise = numerator r
    
    nonAdjacentPairs :: [a] -> [(a,a)]
    nonAdjacentPairs (x1:x2:xs) = [(x1,x3) | x3 <- xs] ++ nonAdjacentPairs (x2:xs)
    nonAdjacentPairs _ = []

    asBin :: Integer.Expr -> SAT.Lit
    asBin (Integer.Expr [(1,[lit])]) = lit
    asBin _ = error "asBin: failure"

-- ------------------------------------------------------------------------

writeSOLFile :: Options -> SAT.Model -> Maybe Integer -> Int -> IO ()
writeSOLFile opt m obj nbvar = do
  case optWriteFile opt of
    Nothing -> return ()
    Just fname -> do
      let m2 = Map.fromList [("x" ++ show x, if b then 1 else 0) | (x,b) <- assocs m, x <= nbvar]
      writeFile fname (GurobiSol.render (Map.map fromInteger m2) (fmap fromInteger obj))
