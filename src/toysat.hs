{-# LANGUAGE ScopedTypeVariables, DoAndIfThenElse, CPP #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  toysat
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (ScopedTypeVariables)
--
-- A toy-level SAT solver based on CDCL.
--
-----------------------------------------------------------------------------

module Main where

import Control.Monad
import Control.Exception
import Data.Array.IArray
import qualified Data.ByteString.Lazy as BS
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntSet as IS
import Data.Char
import Data.IORef
import Data.List
import Data.Maybe
import Data.Ord
import Data.Ratio
import Data.Version
import Data.Time.LocalTime
import Data.Time.Format
import System.IO
import System.Environment
import System.Exit
import System.Locale
import System.Console.GetOpt
import System.CPUTime
import System.FilePath
import System.Timeout
import qualified System.Info as SysInfo
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS
import Text.Printf
#ifdef __GLASGOW_HASKELL__
import GHC.Environment (getFullArgs)
#endif
#ifdef FORCE_CHAR8
import GHC.IO.Encoding
#endif

import Data.ArithRel
import Data.Linear
import qualified SAT
import qualified SAT.PBO as PBO
import qualified SAT.Integer
import qualified SAT.TseitinEncoder as Tseitin
import SAT.Types (pbEval)
import SAT.Printer
import qualified Text.PBFile as PBFile
import qualified Text.LPFile as LPFile
import qualified Text.MPSFile as MPSFile
import qualified Text.MaxSAT as MaxSAT
import qualified Text.GCNF as GCNF
import qualified Text.GurobiSol as GurobiSol
import Version
import Util (showRational, revMapM, revForM)

-- ------------------------------------------------------------------------

data Mode = ModeHelp | ModeVersion | ModeSAT | ModeMUS | ModePB | ModeWBO | ModeMaxSAT | ModeLP

data Options
  = Options
  { optMode          :: Maybe Mode
  , optRestartStrategy :: SAT.RestartStrategy
  , optRestartFirst  :: Int
  , optRestartInc    :: Double
  , optLearningStrategy :: SAT.LearningStrategy
  , optLearntSizeInc :: Double
  , optCCMin         :: Int
  , optRandomFreq    :: Double
  , optRandomSeed    :: Int
  , optLinearizerPB  :: Bool
  , optSearchStrategy       :: PBO.SearchStrategy
  , optObjFunVarsHeuristics :: Bool
  , optPrintRational :: Bool
  , optCheckModel  :: Bool
  , optTimeout :: Integer
  , optWriteFile :: Maybe FilePath
  }

defaultOptions :: Options
defaultOptions
  = Options
  { optMode          = Nothing
  , optRestartStrategy = SAT.defaultRestartStrategy
  , optRestartFirst  = SAT.defaultRestartFirst
  , optRestartInc    = SAT.defaultRestartInc
  , optLearningStrategy = SAT.defaultLearningStrategy
  , optLearntSizeInc = SAT.defaultLearntSizeInc
  , optCCMin         = SAT.defaultCCMin
  , optRandomFreq    = SAT.defaultRandomFreq
  , optRandomSeed    = 0
  , optLinearizerPB  = False
  , optSearchStrategy       = PBO.optSearchStrategy PBO.defaultOptions
  , optObjFunVarsHeuristics = PBO.optObjFunVarsHeuristics PBO.defaultOptions
  , optPrintRational = False  
  , optCheckModel = False
  , optTimeout = 0
  , optWriteFile = Nothing
  }

options :: [OptDescr (Options -> Options)]
options =
    [ Option ['h'] ["help"]   (NoArg (\opt -> opt{ optMode = Just ModeHelp   })) "show help"
    , Option [] ["version"]   (NoArg (\opt -> opt{ optMode = Just ModeVersion})) "show version"

    , Option []    ["sat"]    (NoArg (\opt -> opt{ optMode = Just ModeSAT    })) "solve pseudo boolean problems in .cnf file (default)"
    , Option []    ["mus"]    (NoArg (\opt -> opt{ optMode = Just ModeMUS    })) "solve minimally unsatisfiable subset problems in .gcnf file"
    , Option []    ["pb"]     (NoArg (\opt -> opt{ optMode = Just ModePB     })) "solve pseudo boolean problems in .pb file"
    , Option []    ["wbo"]    (NoArg (\opt -> opt{ optMode = Just ModeWBO    })) "solve weighted boolean optimization problem in .opb file"
    , Option []    ["maxsat"] (NoArg (\opt -> opt{ optMode = Just ModeMaxSAT })) "solve MaxSAT problem in .cnf or .wcnf file"
    , Option []    ["lp"]     (NoArg (\opt -> opt{ optMode = Just ModeLP     })) "solve binary integer programming problem in .lp or .mps file"

    , Option [] ["restart"]
        (ReqArg (\val opt -> opt{ optRestartStrategy = parseRestartStrategy val }) "<str>")
        "Restart startegy: MiniSAT (default), Armin, Luby."
    , Option [] ["restart-first"]
        (ReqArg (\val opt -> opt{ optRestartFirst = read val }) "<integer>")
        (printf "The initial restart limit. (default %d)" SAT.defaultRestartFirst)
    , Option [] ["restart-inc"]
        (ReqArg (\val opt -> opt{ optRestartInc = read val }) "<real>")
        (printf "The factor with which the restart limit is multiplied in each restart. (default %f)" SAT.defaultRestartInc)
    , Option [] ["learning"]
        (ReqArg (\val opt -> opt{ optLearningStrategy = parseLS val }) "<name>")
        "Leaning scheme: clause (default)"
    , Option [] ["learnt-size-inc"]
        (ReqArg (\val opt -> opt{ optLearntSizeInc = read val }) "<real>")
        (printf "The limit for learnt clauses is multiplied with this factor periodically. (default %f)" SAT.defaultLearntSizeInc)
    , Option [] ["ccmin"]
        (ReqArg (\val opt -> opt{ optCCMin = read val }) "<int>")
        (printf "Conflict clause minimization (0=none, 1=local, 2=recursive; default %d)" SAT.defaultCCMin)

    , Option [] ["random-freq"]
        (ReqArg (\val opt -> opt{ optRandomFreq = read val }) "<0..1>")
        (printf "The frequency with which the decision heuristic tries to choose a random variable (default %f)" SAT.defaultRandomFreq)
    , Option [] ["random-seed"]
        (ReqArg (\val opt -> opt{ optRandomSeed = read val }) "<int>")
        "Used by the random variable selection"

    , Option [] ["linearizer-pb"]
        (NoArg (\opt -> opt{ optLinearizerPB = True }))
        "Use PB constraint in linearization."

    , Option [] ["search"]
        (ReqArg (\val opt -> opt{ optSearchStrategy = parseSearch val }) "<str>")
        "Search algorithm used in optimization; linear (default), binary"
    , Option [] ["objfun-heuristics"]
        (NoArg (\opt -> opt{ optObjFunVarsHeuristics = True }))
        "Enable heuristics for polarity/activity of variables in objective function (default)"
    , Option [] ["no-objfun-heuristics"]
        (NoArg (\opt -> opt{ optObjFunVarsHeuristics = False }))
        "Disable heuristics for polarity/activity of variables in objective function"

    , Option [] ["print-rational"]
        (NoArg (\opt -> opt{ optPrintRational = True }))
        "print rational numbers instead of decimals"
    , Option ['w'] []
        (ReqArg (\val opt -> opt{ optWriteFile = Just val }) "<filename>")
        "write model to filename in Gurobi .sol format"

    , Option [] ["check-model"]
        (NoArg (\opt -> opt{ optCheckModel = True }))
        "check model for debug"

    , Option [] ["timeout"]
        (ReqArg (\val opt -> opt{ optTimeout = read val }) "<int>")
        "Kill toysat after given number of seconds (default 0 (no limit))"
    ]
  where
    parseRestartStrategy s =
      case map toLower s of
        "minisat" -> SAT.MiniSATRestarts
        "armin" -> SAT.ArminRestarts
        "luby" -> SAT.LubyRestarts
        _ -> undefined

    parseSearch s =
      case map toLower s of
        "linear" -> PBO.LinearSearch
        "binary" -> PBO.BinarySearch
        _ -> error (printf "unknown search strategy %s" s)

    parseLS "clause" = SAT.LearningClause
    parseLS "hybrid" = SAT.LearningHybrid
    parseLS s = error (printf "unknown learning strategy %s" s)

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setLocaleEncoding char8
  setForeignEncoding char8
  setFileSystemEncoding char8
#endif

  start <- getCPUTime
  args <- getArgs
  case getOpt Permute options args of
    (o,args2,[]) -> do
      printSysInfo
#ifdef __GLASGOW_HASKELL__
      fullArgs <- getFullArgs
#else
      let fullArgs = args
#endif
      printf "c command line = %s\n" (show fullArgs)
      let opt = foldl (flip id) defaultOptions o      
          timelim = optTimeout opt * 10^(6::Int)

      if (timelim > fromIntegral (maxBound :: Int))
       then do
         printf "c TIMEOUT is too long"
         printf "s UNKNOWN"
         exitFailure
       else do
         ret <- timeout (if timelim > 0 then fromIntegral timelim else (-1)) $ do
            solver <- newSolver opt
            let mode =
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
                            ".lp"   -> ModeLP
                            ".mps"  -> ModeLP
                            _ -> ModeSAT
            case mode of
              ModeHelp    -> showHelp stdout
              ModeVersion -> hPutStrLn stdout (showVersion version)
              ModeSAT     -> mainSAT opt solver args2
              ModeMUS     -> mainMUS opt solver args2
              ModePB      -> mainPB opt solver args2
              ModeWBO     -> mainWBO opt solver args2
              ModeMaxSAT  -> mainMaxSAT opt solver args2
              ModeLP      -> mainLP opt solver args2

         when (isNothing ret) $ do
           putStrLn "c TIMEOUT"
           putStrLn "s UNKNOWN"
         end <- getCPUTime
         printf "c total time = %.3fs\n" (fromIntegral (end - start) / 10^(12::Int) :: Double)
         when (isNothing ret) exitFailure

    (_,_,errs) -> do
      mapM_ putStrLn errs
      exitFailure

showHelp :: Handle -> IO ()
showHelp h = hPutStrLn h (usageInfo header options)

header :: String
header = unlines
  [ "Usage:"
  , "  toysat [OPTION]... [file.cnf||-]"
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
  hPrintf stdout "c %s\n" (formatTime defaultTimeLocale "%FT%X%z" tm)
  hPrintf stdout "c arch = %s\n" SysInfo.arch
  hPrintf stdout "c os = %s\n" SysInfo.os
  hPrintf stdout "c compiler = %s %s\n" SysInfo.compilerName (showVersion SysInfo.compilerVersion)
  hPutStrLn stdout "c packages:"
  forM_ packageVersions $ \(package, ver) -> do
    hPrintf stdout "c   %s-%s\n" package ver

newSolver :: Options -> IO SAT.Solver
newSolver opts = do
  solver <- SAT.newSolver
  SAT.setRestartStrategy solver (optRestartStrategy opts)
  SAT.setRestartFirst  solver (optRestartFirst opts)
  SAT.setRestartInc    solver (optRestartInc opts)
  SAT.setLearntSizeInc solver (optLearntSizeInc opts)
  SAT.setCCMin         solver (optCCMin opts)
  SAT.setRandomFreq    solver (optRandomFreq opts)
  when (optRandomSeed opts /= 0) $ 
    SAT.setRandomSeed solver (optRandomSeed opts)
  SAT.setLearningStrategy solver (optLearningStrategy opts)
  SAT.setLogger solver $ \str -> do
    putStr "c "
    putStrLn str
    hFlush stdout
  SAT.setCheckModel solver (optCheckModel opts)
  return solver

-- ------------------------------------------------------------------------

mainSAT :: Options -> SAT.Solver -> [String] -> IO ()
mainSAT opt solver args = do
  ret <- case args of
           ["-"]   -> fmap (DIMACS.parseByteString "-") $ BS.hGetContents stdin
           [fname] -> DIMACS.parseFile fname
           _ -> showHelp stderr >> exitFailure
  case ret of
    Left err -> hPrint stderr err >> exitFailure
    Right cnf -> solveSAT opt solver cnf

solveSAT :: Options -> SAT.Solver -> DIMACS.CNF -> IO ()
solveSAT opt solver cnf = do
  printf "c #vars %d\n" (DIMACS.numVars cnf)
  printf "c #constraints %d\n" (length (DIMACS.clauses cnf))
  _ <- replicateM (DIMACS.numVars cnf) (SAT.newVar solver)
  forM_ (DIMACS.clauses cnf) $ \clause ->
    SAT.addClause solver (elems clause)
  result <- SAT.solve solver
  putStrLn $ "s " ++ (if result then "SATISFIABLE" else "UNSATISFIABLE")
  hFlush stdout
  when result $ do
    m <- SAT.model solver
    satPrintModel stdout m (DIMACS.numVars cnf)
    writeSOLFile opt m Nothing (DIMACS.numVars cnf)

-- ------------------------------------------------------------------------

mainMUS :: Options -> SAT.Solver -> [String] -> IO ()
mainMUS opt solver args = do
  gcnf <- case args of
           ["-"]   -> fmap GCNF.parseString $ hGetContents stdin
           [fname] -> GCNF.parseFile fname
           _ -> showHelp stderr >> exitFailure
  solveMUS opt solver gcnf

solveMUS :: Options -> SAT.Solver -> GCNF.GCNF -> IO ()
solveMUS opt solver gcnf = do
  printf "c #vars %d\n" (GCNF.nbvar gcnf)
  printf "c #constraints %d\n" (length (GCNF.clauses gcnf))
  printf "c #groups %d\n" (GCNF.lastgroupindex gcnf)

  _ <- replicateM (GCNF.nbvar gcnf) (SAT.newVar solver)

  tbl <- forM [1 .. GCNF.lastgroupindex gcnf] $ \i -> do
    sel <- SAT.newVar solver
    return (i, sel)
  let idx2sel :: Array Int SAT.Var
      idx2sel = array (1, GCNF.lastgroupindex gcnf) tbl
      selrng  = if null tbl then (0,-1) else (snd $ head tbl, snd $ last tbl)
      sel2idx :: Array SAT.Lit Int
      sel2idx = array selrng [(sel, idx) | (idx, sel) <- tbl]

  forM_ (GCNF.clauses gcnf) $ \(idx, clause) ->
    if idx==0
    then SAT.addClause solver clause
    else SAT.addClause solver (- (idx2sel ! idx) : clause)

  result <- SAT.solveWith solver (map (idx2sel !) [1..GCNF.lastgroupindex gcnf])
  putStrLn $ "s " ++ (if result then "SATISFIABLE" else "UNSATISFIABLE")
  hFlush stdout

  if result
    then do
      m <- SAT.model solver
      satPrintModel stdout m (GCNF.nbvar gcnf)
      writeSOLFile opt m Nothing (GCNF.nbvar gcnf)
    else do
      putStrLn "c computing a minimally unsatisfiable subformula"
      hFlush stdout

      let loop core fixed = do
            let is = core `IS.difference` fixed
            if IS.null is
              then return core
              else do
                let i2:is2 = IS.toList is
                putStrLn $ "c core = {" ++ intercalate ", " (map show (IS.toList core)) ++ "}"
                putStrLn $ "c trying to remove " ++ show i2
                hFlush stdout
                ret <- SAT.solveWith solver (map (idx2sel !) is2)
                if not ret
                  then do
                    putStrLn $ "c successed to remove " ++ show i2
                    ls2 <- SAT.getBadAssumptions solver
                    let core2 = IS.map (sel2idx !) ls2 `IS.union` fixed
                    loop core2 fixed
                  else do
                    putStrLn $ "c failed to remove " ++ show i2
                    SAT.addClause solver [idx2sel ! i2]
                    loop core (IS.insert i2 fixed)

      ls <- SAT.getBadAssumptions solver
      let core = IS.map (sel2idx !) ls
      core2 <- loop core IS.empty

      musPrintSol stdout (IS.toList core2)

-- ------------------------------------------------------------------------

mainPB :: Options -> SAT.Solver -> [String] -> IO ()
mainPB opt solver args = do
  ret <- case args of
           ["-"]   -> fmap (PBFile.parseOPBString "-") $ hGetContents stdin
           [fname] -> PBFile.parseOPBFile fname
           _ -> showHelp stderr >> exitFailure
  case ret of
    Left err -> hPrint stderr err >> exitFailure
    Right formula -> solvePB opt solver formula

solvePB :: Options -> SAT.Solver -> PBFile.Formula -> IO ()
solvePB opt solver formula@(obj, cs) = do
  let n = PBFile.pbNumVars formula

  printf "c #vars %d\n" n
  printf "c #constraints %d\n" (length cs)

  _ <- replicateM n (SAT.newVar solver)
  enc <- Tseitin.newEncoder solver
  Tseitin.setUsePB enc (optLinearizerPB opt)

  forM_ cs $ \(lhs, op, rhs) -> do
    lhs' <- pbConvSum enc lhs
    case op of
      PBFile.Ge -> SAT.addPBAtLeast solver lhs' rhs
      PBFile.Eq -> SAT.addPBExactly solver lhs' rhs

  case obj of
    Nothing -> do
      result <- SAT.solve solver
      putStrLn $ "s " ++ (if result then "SATISFIABLE" else "UNSATISFIABLE")
      hFlush stdout
      when result $ do
        m <- SAT.model solver
        pbPrintModel stdout m n
        writeSOLFile opt m Nothing n

    Just obj' -> do
      obj'' <- pbConvSum enc obj'

      modelRef <- newIORef Nothing

      result <- try $ minimize opt solver obj'' $ \m val -> do
        writeIORef modelRef (Just m)
        putStrLn $ "o " ++ show val
        hFlush stdout

      case result of
        Right Nothing -> do
          putStrLn $ "s " ++ "UNSATISFIABLE"
          hFlush stdout
        Right (Just m) -> do
          putStrLn $ "s " ++ "OPTIMUM FOUND"
          hFlush stdout
          pbPrintModel stdout m n
          let objval = pbEval m obj''
          writeSOLFile opt m (Just objval) n
        Left (e :: AsyncException) -> do
          r <- readIORef modelRef
          case r of
            Nothing -> do
              putStrLn $ "s " ++ "UNKNOWN"
              hFlush stdout
            Just m -> do
              putStrLn $ "s " ++ "SATISFIABLE"
              pbPrintModel stdout m n
              let objval = pbEval m obj''
              writeSOLFile opt m (Just objval) n
          throwIO e

pbConvSum :: Tseitin.Encoder -> PBFile.Sum -> IO [(Integer, SAT.Lit)]
pbConvSum enc = revMapM f
  where
    f (w,ls) = do
      l <- Tseitin.encodeConj enc ls
      return (w,l)

minimize :: Options -> SAT.Solver -> [(Integer, SAT.Lit)] -> (SAT.Model -> Integer -> IO ()) -> IO (Maybe SAT.Model)
minimize opt solver obj update = do
  let opt2 =
        PBO.defaultOptions
        { PBO.optObjFunVarsHeuristics = optObjFunVarsHeuristics opt
        , PBO.optSearchStrategy       = optSearchStrategy opt
        , PBO.optLogger  = \s -> putStr "c " >> putStrLn s
        , PBO.optUpdater = update
        }
  PBO.minimize solver obj opt2

-- ------------------------------------------------------------------------

mainWBO :: Options -> SAT.Solver -> [String] -> IO ()
mainWBO opt solver args = do
  ret <- case args of
           ["-"]   -> fmap (PBFile.parseWBOString "-") $ hGetContents stdin
           [fname] -> PBFile.parseWBOFile fname
           _ -> showHelp stderr >> exitFailure
  case ret of
    Left err -> hPrint stderr err >> exitFailure
    Right formula -> solveWBO opt solver False formula

solveWBO :: Options -> SAT.Solver -> Bool -> PBFile.SoftFormula -> IO ()
solveWBO opt solver isMaxSat formula@(tco, cs) = do
  let nvar = PBFile.wboNumVars formula
  printf "c #vars %d\n" nvar
  printf "c #constraints %d\n" (length cs)

  _ <- replicateM nvar (SAT.newVar solver)
  enc <- Tseitin.newEncoder solver
  Tseitin.setUsePB enc (optLinearizerPB opt)

  obj <- liftM concat $ revForM cs $ \(cost, (lhs, op, rhs)) -> do
    lhs' <- pbConvSum enc lhs
    case cost of
      Nothing -> do
        case op of
          PBFile.Ge -> SAT.addPBAtLeast solver lhs' rhs
          PBFile.Eq -> SAT.addPBExactly solver lhs' rhs
        return []
      Just cval -> do
        sel <- SAT.newVar solver
        case op of
          PBFile.Ge -> SAT.addPBAtLeastSoft solver sel lhs' rhs
          PBFile.Eq -> SAT.addPBExactlySoft solver sel lhs' rhs
        return [(cval, SAT.litNot sel)]

  case tco of
    Nothing -> return ()
    Just c -> SAT.addPBAtMost solver obj (c-1)

  modelRef <- newIORef Nothing
  result <- try $ minimize opt solver obj $ \m val -> do
     writeIORef modelRef (Just m)
     putStrLn $ "o " ++ show val
     hFlush stdout

  case result of
    Right Nothing -> do
      putStrLn $ "s " ++ "UNSATISFIABLE"
      hFlush stdout
    Right (Just m) -> do
      putStrLn $ "s " ++ "OPTIMUM FOUND"
      hFlush stdout
      if isMaxSat
        then maxsatPrintModel stdout m nvar
        else pbPrintModel stdout m nvar
      let objval = pbEval m obj
      writeSOLFile opt m (Just objval) nvar
    Left (e :: AsyncException) -> do
      r <- readIORef modelRef
      case r of
        Just m | not isMaxSat -> do
          putStrLn $ "s " ++ "SATISFIABLE"
          pbPrintModel stdout m nvar
          let objval = pbEval m obj
          writeSOLFile opt m (Just objval) nvar
        _ -> do
          putStrLn $ "s " ++ "UNKNOWN"
          hFlush stdout
      throwIO e

-- ------------------------------------------------------------------------

mainMaxSAT :: Options -> SAT.Solver -> [String] -> IO ()
mainMaxSAT opt solver args = do
  s <- case args of
         ["-"]   -> getContents
         [fname] -> readFile fname
         _ -> showHelp stderr  >> exitFailure
  let wcnf = MaxSAT.parseWCNFString s
  solveMaxSAT opt solver wcnf

solveMaxSAT :: Options -> SAT.Solver -> MaxSAT.WCNF -> IO ()
solveMaxSAT opt solver (_, top, cs) = do
  solveWBO opt solver True
           ( Nothing
           , [ (if w >= top then Nothing else Just w
             , ([(1,[lit]) | lit<-lits], PBFile.Ge, 1))
             | (w,lits) <- cs
             ]
           )

-- ------------------------------------------------------------------------

mainLP :: Options -> SAT.Solver -> [String] -> IO ()
mainLP opt solver args = do
  (fname,s) <-
    case args of
      ["-"]   -> do
        s <- hGetContents stdin
        return ("-", s)
      [fname] -> do
        s <- readFile fname
        return (fname, s)
      _ -> showHelp stderr >> exitFailure
  lp <-
    case LPFile.parseString fname s of
      Right lp -> return lp
      Left err ->
        case MPSFile.parseString fname s of
          Right lp -> return lp
          Left err2 -> do
            hPrint stderr err
            hPrint stderr err2
            exitFailure
  solveLP opt solver lp

solveLP :: Options -> SAT.Solver -> LPFile.LP -> IO ()
solveLP opt solver lp = do
  if not (Set.null nivs)
    then do
      putStrLn $ "c cannot handle non-integer variables: " ++ intercalate ", " (Set.toList nivs)
      putStrLn "s UNKNOWN"
      exitFailure
    else do
      enc <- Tseitin.newEncoder solver
      Tseitin.setUsePB enc (optLinearizerPB opt)

      putStrLn "c Loading variables and bounds"
      vmap <- liftM Map.fromList $ revForM (Set.toList ivs) $ \v -> do
        let (lb,ub) = LPFile.getBounds lp v
        case (lb,ub) of
          (LPFile.Finite lb', LPFile.Finite ub') -> do
            v2 <- SAT.Integer.newVar solver (ceiling lb') (floor ub')
            return (v,v2)
          _ -> do
            putStrLn $ "c cannot handle unbounded variable: " ++ v
            putStrLn "s UNKNOWN"
            exitFailure

      putStrLn "c Loading constraints"
      forM_ (LPFile.constraints lp) $ \c -> do
        let indicator      = LPFile.constrIndicator c
            (lhs, op, rhs) = LPFile.constrBody c
        let d = foldl' lcm 1 (map denominator  (rhs:[r | LPFile.Term r _ <- lhs]))
            lhs' = lsum [asInteger (r * fromIntegral d) .*. product [vmap Map.! v | v <- vs] | LPFile.Term r vs <- lhs]
            rhs' = asInteger (rhs * fromIntegral d)
        case indicator of
          Nothing ->
            case op of
              LPFile.Le  -> SAT.Integer.addConstraint enc $ lhs' .<=. fromInteger rhs'
              LPFile.Ge  -> SAT.Integer.addConstraint enc $ lhs' .>=. fromInteger rhs'
              LPFile.Eql -> SAT.Integer.addConstraint enc $ lhs' .==. fromInteger rhs'
          Just (var, val) -> do
            let var' = asBin (vmap Map.! var)
                f sel = do
                  case op of
                    LPFile.Le  -> SAT.Integer.addConstraintSoft enc sel $ lhs' .<=. fromInteger rhs'
                    LPFile.Ge  -> SAT.Integer.addConstraintSoft enc sel $ lhs' .>=. fromInteger rhs'
                    LPFile.Eql -> SAT.Integer.addConstraintSoft enc sel $ lhs' .==. fromInteger rhs'
            case val of
              1 -> f var'
              0 -> f (SAT.litNot var')
              _ -> return ()

      putStrLn "c Loading SOS constraints"
      forM_ (LPFile.sos lp) $ \(_label, typ, xs) -> do
        case typ of
          LPFile.S1 -> SAT.addAtMost solver (map (asBin . (vmap Map.!) . fst) xs) 1
          LPFile.S2 -> do
            let ps = nonAdjacentPairs $ map fst $ sortBy (comparing snd) $ xs
            forM_ ps $ \(x1,x2) -> do
              SAT.addClause solver [SAT.litNot $ asBin $ vmap Map.! v | v <- [x1,x2]]

      let (_label,obj) = LPFile.objectiveFunction lp      
          d = foldl' lcm 1 [denominator r | LPFile.Term r _ <- obj] *
              (if LPFile.dir lp == LPFile.OptMin then 1 else -1)
          obj2 = lsum [asInteger (r * fromIntegral d) .*. product [vmap Map.! v | v <- vs] | LPFile.Term r vs <- obj]
      (obj3,obj3_c) <- SAT.Integer.linearize enc obj2

      modelRef <- newIORef Nothing

      result <- try $ minimize opt solver obj3 $ \m val -> do
        writeIORef modelRef (Just m)
        putStrLn $ "o " ++ showRational (optPrintRational opt) (fromIntegral (val + obj3_c) / fromIntegral d)
        hFlush stdout

      let printModel :: SAT.Model -> IO ()
          printModel m = do
            forM_ (Set.toList ivs) $ \v -> do
              let val = SAT.Integer.eval m (vmap Map.! v)
              printf "v %s = %d\n" v val
            hFlush stdout
            writeSol m

          writeSol :: SAT.Model -> IO ()
          writeSol m = do
            case optWriteFile opt of
              Nothing -> return ()
              Just fname -> do
                let m2 = Map.fromList [ (v, fromInteger val)     
                                      | v <- Set.toList ivs
                                      , let val = SAT.Integer.eval m (vmap Map.! v) ]
                    o  = fromInteger $ SAT.Integer.eval m obj2
                writeFile fname (GurobiSol.render m2 (Just o))

      case result of
        Right Nothing -> do
          putStrLn $ "s " ++ "UNSATISFIABLE"
          hFlush stdout
        Right (Just m) -> do
          putStrLn $ "s " ++ "OPTIMUM FOUND"
          hFlush stdout
          printModel m
        Left (e :: AsyncException) -> do
          r <- readIORef modelRef
          case r of
            Nothing -> do
              putStrLn $ "s " ++ "UNKNOWN"
              hFlush stdout
            Just m -> do
              putStrLn $ "s " ++ "SATISFIABLE"
              printModel m
          throwIO e
  where
    ivs = LPFile.binaryVariables lp `Set.union` LPFile.integerVariables lp
    nivs = LPFile.variables lp `Set.difference` ivs

    asInteger :: Rational -> Integer
    asInteger r
      | denominator r /= 1 = error (show r ++ " is not integer")
      | otherwise = numerator r
    
    nonAdjacentPairs :: [a] -> [(a,a)]
    nonAdjacentPairs (x1:x2:xs) = [(x1,x3) | x3 <- xs] ++ nonAdjacentPairs (x2:xs)
    nonAdjacentPairs _ = []

    asBin :: SAT.Integer.Expr -> SAT.Lit
    asBin (SAT.Integer.Expr [(1,[lit])]) = lit
    asBin _ = error "asBin: failure"

-- ------------------------------------------------------------------------

writeSOLFile :: Options -> SAT.Model -> Maybe Integer -> Int -> IO ()
writeSOLFile opt m obj nbvar = do
  case optWriteFile opt of
    Nothing -> return ()
    Just fname -> do
      let m2 = Map.fromList [("x" ++ show x, if b then 1 else 0) | (x,b) <- assocs m, x <= nbvar]
      writeFile fname (GurobiSol.render (Map.map fromInteger m2) (fmap fromInteger obj))
