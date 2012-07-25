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

import Data.Linear
import qualified SAT
import qualified SAT.Integer
import qualified SAT.Linearizer as Lin
import SAT.Types (pbEval, pbLowerBound)
import SAT.Printer
import qualified Text.PBFile as PBFile
import qualified Text.LPFile as LPFile
import qualified Text.MaxSAT as MaxSAT
import Version
import Util (showRational, revMapM, revForM)

-- ------------------------------------------------------------------------

data Mode = ModeHelp | ModeVersion | ModeSAT | ModePB | ModeWBO | ModeMaxSAT | ModeLP

data Options
  = Options
  { optMode          :: Mode
  , optRestartStrategy :: SAT.RestartStrategy
  , optRestartFirst  :: Int
  , optRestartInc    :: Double
  , optLearningStrategy :: SAT.LearningStrategy
  , optLearntSizeInc :: Double
  , optCCMin         :: Int
  , optRandomFreq    :: Double
  , optRandomSeed    :: Int
  , optLinearizerPB  :: Bool
  , optBinarySearch  :: Bool
  , optObjFunVarsHeuristics :: Bool
  , optPrintRational :: Bool
  , optCheckModel  :: Bool
  , optTimeout :: Integer
  }

defaultOptions :: Options
defaultOptions
  = Options
  { optMode          = ModeSAT
  , optRestartStrategy = SAT.defaultRestartStrategy
  , optRestartFirst  = SAT.defaultRestartFirst
  , optRestartInc    = SAT.defaultRestartInc
  , optLearningStrategy = SAT.defaultLearningStrategy
  , optLearntSizeInc = SAT.defaultLearntSizeInc
  , optCCMin         = SAT.defaultCCMin
  , optRandomFreq    = SAT.defaultRandomFreq
  , optRandomSeed    = 0
  , optLinearizerPB  = False
  , optBinarySearch   = False
  , optObjFunVarsHeuristics = True
  , optPrintRational = False  
  , optCheckModel = False
  , optTimeout = 0
  }

options :: [OptDescr (Options -> Options)]
options =
    [ Option ['h'] ["help"]   (NoArg (\opt -> opt{ optMode = ModeHelp   })) "show help"
    , Option [] ["version"]   (NoArg (\opt -> opt{ optMode = ModeVersion})) "show version"

    , Option []    ["pb"]     (NoArg (\opt -> opt{ optMode = ModePB     })) "solve pseudo boolean problems in .pb file"
    , Option []    ["wbo"]    (NoArg (\opt -> opt{ optMode = ModeWBO    })) "solve weighted boolean optimization problem in .opb file"
    , Option []    ["maxsat"] (NoArg (\opt -> opt{ optMode = ModeMaxSAT })) "solve MaxSAT problem in .cnf or .wcnf file"
    , Option []    ["lp"]     (NoArg (\opt -> opt{ optMode = ModeLP     })) "solve binary integer programming problem in .lp file"

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
        (ReqArg (\val opt -> opt{ optBinarySearch = parseSearch val }) "<str>")
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
        "linear" -> False
        "binary" -> True
        _ -> undefined

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
            case optMode opt of
              ModeHelp    -> showHelp stdout
              ModeVersion -> hPutStrLn stdout (showVersion version)
              ModeSAT     -> mainSAT opt solver args2
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
  , "  toysat [OPTION]... --pb [file.opb|-]"
  , "  toysat [OPTION]... --wbo [file.wbo|-]"
  , "  toysat [OPTION]... --maxsat [file.cnf|file.wcnf|-]"
  , "  toysat [OPTION]... --lp [file.lp|-]"
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
solveSAT _ solver cnf = do
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
  lin <- Lin.newLinearizer solver
  Lin.setUsePB lin (optLinearizerPB opt)

  forM_ cs $ \(lhs, op, rhs) -> do
    lhs' <- pbConvSum lin lhs
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

    Just obj' -> do
      obj'' <- pbConvSum lin obj'

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
        Left (e :: AsyncException) -> do
          r <- readIORef modelRef
          case r of
            Nothing -> do
              putStrLn $ "s " ++ "UNKNOWN"
              hFlush stdout
            Just m -> do
              putStrLn $ "s " ++ "SATISFIABLE"
              pbPrintModel stdout m n
          throwIO e

pbConvSum :: Lin.Linearizer -> PBFile.Sum -> IO [(Integer, SAT.Lit)]
pbConvSum lin = revMapM f
  where
    f (w,ls) = do
      l <- Lin.translate lin ls
      return (w,l)

minimize :: Options -> SAT.Solver -> [(Integer, SAT.Lit)] -> (SAT.Model -> Integer -> IO ()) -> IO (Maybe SAT.Model)
minimize opt solver obj update = do
  when (optObjFunVarsHeuristics opt) $ do
    forM_ obj $ \(c,l) -> do
      let p = if c > 0 then not (SAT.litPolarity l) else SAT.litPolarity l
      SAT.setVarPolarity solver (SAT.litVar l) p
    forM_ (zip [1..] (map snd (sortBy (comparing fst) [(abs c, l) | (c,l) <- obj]))) $ \(n,l) -> do
      replicateM n $ SAT.varBumpActivity solver (SAT.litVar l)

  result <- SAT.solve solver
  if not result then
    return Nothing
  else if optBinarySearch opt then
    liftM Just binSearch 
  else
    liftM Just linSearch

  where
   linSearch :: IO SAT.Model
   linSearch = do
     m <- SAT.model solver
     let v = pbEval m obj
     update m v
     SAT.addPBAtMost solver obj (v - 1)
     result <- SAT.solve solver
     if result
       then linSearch
       else return m

   binSearch :: IO SAT.Model
   binSearch = do
{-
     printf "c Binary Search: minimizing %s \n" $ 
       intercalate " "
         [c' ++ " " ++ l'
         | (c,l) <- obj
         , let c' = if c < 0 then show c else "+" ++ show c
         , let l' = (if l < 0 then "~" else "") ++ "x" ++ show (SAT.litVar l)
         ]
-}
     m0 <- SAT.model solver
     let v0 = pbEval m0 obj
     update m0 v0
     let ub0 = v0 - 1
         lb0 = pbLowerBound obj
     SAT.addPBAtMost solver obj ub0

     let loop lb ub m | ub < lb = return m
         loop lb ub m = do
           let mid = (lb + ub) `div` 2
           printf "c Binary Search: %d <= obj <= %d; guessing obj <= %d\n" lb ub mid
           sel <- SAT.newVar solver
           SAT.addPBAtMostSoft solver sel obj mid
           ret <- SAT.solveWith solver [sel]
           if ret
           then do
             m2 <- SAT.model solver
             let v = pbEval m2 obj
             update m2 v
             -- deactivating temporary constraint
             -- FIXME: –{—ˆ‚Í§–ñ‚Ìíœ‚ð‚µ‚½‚¢
             SAT.addClause solver [-sel]
             let ub' = v - 1
             printf "c Binary Search: updating upper bound: %d -> %d\n" ub ub'
             SAT.addPBAtMost solver obj ub'
             loop lb ub' m2
           else do
             -- deactivating temporary constraint
             -- FIXME: –{—ˆ‚Í§–ñ‚Ìíœ‚ð‚µ‚½‚¢
             SAT.addClause solver [-sel]
             let lb' = mid + 1
             printf "c Binary Search: updating lower bound: %d -> %d\n" lb lb'
             SAT.addPBAtLeast solver obj lb'
             loop lb' ub m

     loop lb0 ub0 m0

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
  lin <- Lin.newLinearizer solver
  Lin.setUsePB lin (optLinearizerPB opt)

  obj <- liftM concat $ revForM cs $ \(cost, (lhs, op, rhs)) -> do
    lhs' <- pbConvSum lin lhs
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
    Left (e :: AsyncException) -> do
      r <- readIORef modelRef
      case r of
        Just m | not isMaxSat -> do
          putStrLn $ "s " ++ "SATISFIABLE"
          pbPrintModel stdout m nvar
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
  ret <- case args of
           ["-"]   -> fmap (LPFile.parseString "-") $ hGetContents stdin
           [fname] -> LPFile.parseFile fname
           _ -> showHelp stderr >> exitFailure
  case ret of
    Left err -> hPrint stderr err >> exitFailure
    Right lp -> solveLP opt solver lp

solveLP :: Options -> SAT.Solver -> LPFile.LP -> IO ()
solveLP opt solver lp = do
  if not (Set.null nivs)
    then do
      putStrLn $ "c cannot handle non-integer variables: " ++ intercalate ", " (Set.toList nivs)
      putStrLn "s UNKNOWN"
      exitFailure
    else do
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
            lhs' = lsum [asInteger (r * fromIntegral d) .*. (vmap Map.! asSingleton vs) | LPFile.Term r vs <- lhs]
            rhs' = asInteger (rhs * fromIntegral d)
        case indicator of
          Nothing ->
            case op of
              LPFile.Le  -> SAT.Integer.addLe solver lhs' (SAT.Integer.constant rhs')
              LPFile.Ge  -> SAT.Integer.addGe solver lhs' (SAT.Integer.constant rhs')
              LPFile.Eql -> SAT.Integer.addEq solver lhs' (SAT.Integer.constant rhs')
          Just (var, val) -> do
            let var' = asBin (vmap Map.! var)
                f sel = do
                  case op of
                    LPFile.Le  -> SAT.Integer.addLeSoft solver sel lhs' (SAT.Integer.constant rhs')
                    LPFile.Ge  -> SAT.Integer.addGeSoft solver sel lhs' (SAT.Integer.constant rhs')
                    LPFile.Eql -> SAT.Integer.addEqSoft solver sel lhs' (SAT.Integer.constant rhs')
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
          obj2 = lsum [asInteger (r * fromIntegral d) .*. (vmap Map.! (asSingleton vs)) | LPFile.Term r vs <- obj]
          SAT.Integer.Expr obj3 obj3_c = obj2

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

    asSingleton :: [a] -> a
    asSingleton [v] = v
    asSingleton _ = error "not a singleton"

    asInteger :: Rational -> Integer
    asInteger r
      | denominator r /= 1 = error (show r ++ " is not integer")
      | otherwise = numerator r
    
    nonAdjacentPairs :: [a] -> [(a,a)]
    nonAdjacentPairs (x1:x2:xs) = [(x1,x3) | x3 <- xs] ++ nonAdjacentPairs (x2:xs)
    nonAdjacentPairs _ = []

    asBin :: SAT.Integer.Expr -> SAT.Lit
    asBin (SAT.Integer.Expr [(1,lit)] _) = lit
    asBin _ = error "asBin: failure"

-- ------------------------------------------------------------------------

