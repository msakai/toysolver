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
import qualified Data.IntMap as IM
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Char
import Data.IORef
import Data.Function
import Data.List
import Data.Maybe
import Data.Ratio
import Data.Version
import Data.Time.LocalTime
import Data.Time.Format
import System.IO
import System.Environment
import System.Exit
import System.Locale
import System.Console.GetOpt
import qualified System.Info as SysInfo
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS
import Text.Printf
#ifdef __GLASGOW_HASKELL__
import GHC.Environment (getFullArgs)
#endif

import qualified SAT
import qualified PBFile
import qualified LPFile
import qualified Linearizer as Lin

-- ------------------------------------------------------------------------

data Mode = ModeHelp | ModeSAT | ModePB | ModeWBO | ModeMaxSAT | ModeLP

data Options
  = Options
  { optMode          :: Mode
  , optRestartStrategy :: SAT.RestartStrategy
  , optRestartFirst  :: Int
  , optRestartInc    :: Double
  , optLearntSizeInc :: Double
  , optCCMin         :: Int
  , optLinearizerPB  :: Bool
  , optBinarySearch  :: Bool
  , optObjFunVarsHeuristics :: Bool
  }

defaultOptions :: Options
defaultOptions
  = Options
  { optMode          = ModeSAT
  , optRestartStrategy = SAT.defaultRestartStrategy
  , optRestartFirst  = SAT.defaultRestartFirst
  , optRestartInc    = SAT.defaultRestartInc
  , optLearntSizeInc = SAT.defaultLearntSizeInc
  , optCCMin         = SAT.defaultCCMin
  , optLinearizerPB  = False
  , optBinarySearch   = False
  , optObjFunVarsHeuristics = True
  }

options :: [OptDescr (Options -> Options)]
options =
    [ Option ['h'] ["help"]   (NoArg (\opt -> opt{ optMode = ModeHelp   })) "show help"
    , Option []    ["pb"]     (NoArg (\opt -> opt{ optMode = ModePB     })) "solve pseudo boolean problems in .pb file"
    , Option []    ["wbo"]    (NoArg (\opt -> opt{ optMode = ModeWBO    })) "solve weighted boolean optimization problem in .opb file"
    , Option []    ["maxsat"] (NoArg (\opt -> opt{ optMode = ModeMaxSAT })) "solve MaxSAT problem in .cnf or .wcnf file"
    , Option []    ["lp"]     (NoArg (\opt -> opt{ optMode = ModeLP     })) "solve binary integer programming problem in .lp file"

    , Option [] ["restart"]
        (ReqArg (\val opt -> opt{ optRestartStrategy = parseRestartStrategy val }) "<str>")
        "Restart startegy: MiniSAT (default), Armin."
    , Option [] ["restart-first"]
        (ReqArg (\val opt -> opt{ optRestartFirst = read val }) "<integer>")
        (printf "The initial restart limit. (default %d)" SAT.defaultRestartFirst)
    , Option [] ["restart-inc"]
        (ReqArg (\val opt -> opt{ optRestartInc = read val }) "<real>")
        (printf "The factor with which the restart limit is multiplied in each restart. (default %f)" SAT.defaultRestartInc)
    , Option [] ["learnt-size-inc"]
        (ReqArg (\val opt -> opt{ optLearntSizeInc = read val }) "<real>")
        (printf "The limit for learnt clauses is multiplied with this factor each restart. (default %f)" SAT.defaultLearntSizeInc)
    , Option [] ["ccmin"]
        (ReqArg (\val opt -> opt{ optCCMin = read val }) "<int>")
        (printf "Conflict clause minimization (0=none, 1=local, 2=recursive; default %d)" SAT.defaultCCMin)

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
    ]
  where
    parseRestartStrategy s =
      case map toLower s of
        "minisat" -> SAT.MiniSATRestarts
        "armin" -> SAT.ArminRestarts
        _ -> undefined

    parseSearch s =
      case map toLower s of
        "linear" -> False
        "binary" -> True
        _ -> undefined

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (o,args2,[]) -> do
      printSysInfo
#ifdef __GLASGOW_HASKELL__
      args <- getFullArgs
#endif
      printf "c command line = %s\n" (show args)
      let opt = foldl (flip id) defaultOptions o
      solver <- newSolver opt
      case optMode opt of
        ModeHelp   -> showHelp stdout
        ModeSAT    -> mainSAT opt solver args2
        ModePB     -> mainPB opt solver args2
        ModeWBO    -> mainWBO opt solver args2
        ModeMaxSAT -> mainMaxSAT opt solver args2
        ModeLP     -> mainLP opt solver args2
    (_,_,errs) -> do
      mapM_ putStrLn errs
      exitFailure

showHelp :: Handle -> IO ()
showHelp h = hPutStrLn h (usageInfo header options)

header :: String
header = unlines
  [ "Usage:"
  , "  toysat [file.cnf||-]"
  , "  toysat --pb [file.opb|-]"
  , "  toysat --wbo [file.wbo|-]"
  , "  toysat --maxsat [file.cnf|file.wcnf|-]"
  , "  toysat --lp [file.lp|-]"
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

newSolver :: Options -> IO SAT.Solver
newSolver opts = do
  solver <- SAT.newSolver
  SAT.setRestartStrategy solver (optRestartStrategy opts)
  SAT.setRestartFirst  solver (optRestartFirst opts)
  SAT.setRestartInc    solver (optRestartInc opts)
  SAT.setLearntSizeInc solver (optLearntSizeInc opts)
  SAT.setCCMin         solver (optCCMin opts)
  SAT.setLogger solver $ \str -> do
    putStr "c "
    putStrLn str
    hFlush stdout
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
    satPrintModel m

satPrintModel :: SAT.Model -> IO ()
satPrintModel m = do
  forM_ (split 10 (IM.toList m)) $ \xs -> do
    putStr "v"
    forM_ xs $ \(var,val) -> putStr (' ': show (SAT.literal var val))
    putStrLn ""
  putStrLn "v 0"
  hFlush stdout

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
  let n = pbNumVars formula

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
        let m2 = IM.filterWithKey (\v _ -> v <= n) m
        pbPrintModel m2

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
          let m2 = IM.filterWithKey (\v _ -> v <= n) m
          pbPrintModel m2
        Left (e :: AsyncException) -> do
          r <- readIORef modelRef
          case r of
            Nothing -> do
              putStrLn $ "s " ++ "UNKNOWN"
              hFlush stdout
            Just m -> do
              putStrLn $ "s " ++ "SATISFIABLE"
              let m2 = IM.filterWithKey (\v _ -> v <= n) m
              pbPrintModel m2
          throwIO e

pbConvSum :: Lin.Linearizer -> PBFile.Sum -> IO [(Integer, SAT.Lit)]
pbConvSum lin = mapM f
  where
    f (w,ls) = do
      l <- Lin.translate lin ls
      return (w,l)

pbLowerBound :: [(Integer, SAT.Lit)] -> Integer
pbLowerBound xs = sum [if c < 0 then c else 0 | (c,_) <- xs]

minimize :: Options -> SAT.Solver -> [(Integer, SAT.Lit)] -> (SAT.Model -> Integer -> IO ()) -> IO (Maybe SAT.Model)
minimize opt solver obj update = do
  when (optObjFunVarsHeuristics opt) $ do
    forM_ obj $ \(c,l) -> do
      let p = if c > 0 then not (SAT.litPolarity l) else SAT.litPolarity l
      SAT.setVarPolarity solver (SAT.litVar l) p
    forM_ (zip [1..] (map snd (sortBy (compare `on` fst) [(abs c, l) | (c,l) <- obj]))) $ \(n,l) -> do
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
     m <- SAT.model solver
     let v = pbEval m obj
     update m v
     let ub = v - 1
     SAT.addPBAtMost solver obj ub

     let loop lb ub m | ub < lb = return m
         loop lb ub m = do
           let mid = (lb + ub) `div` 2
           printf "c Binary Search: %d <= obj <= %d; guessing obj <= %d\n" lb ub mid
           sel <- SAT.newVar solver
           addPBAtMostSoft solver sel obj mid
           ret <- SAT.solveWith solver [sel]
           if ret
           then do
             m <- SAT.model solver
             let v = pbEval m obj
             update m v
             -- deactivating temporary constraint
             -- FIXME: –{—ˆ‚Í§–ñ‚Ìíœ‚ð‚µ‚½‚¢
             SAT.addClause solver [-sel]
             let ub' = v - 1
             printf "c Binary Search: updating upper bound: %d -> %d\n" ub ub'
             SAT.addPBAtMost solver obj ub'
             loop lb ub' m
           else do
             -- deactivating temporary constraint
             -- FIXME: –{—ˆ‚Í§–ñ‚Ìíœ‚ð‚µ‚½‚¢
             SAT.addClause solver [-sel]
             let lb' = mid + 1
             printf "c Binary Search: updating lower bound: %d -> %d\n" lb lb'
             SAT.addPBAtLeast solver obj lb'
             loop lb' ub m

     loop (pbLowerBound obj) (v - 1) m

pbEval :: SAT.Model -> [(Integer, SAT.Lit)] -> Integer
pbEval m xs = sum [c | (c,lit) <- xs, m IM.! SAT.litVar lit == SAT.litPolarity lit]

pbNumVars :: PBFile.Formula -> Int
pbNumVars (m, cs) = maximum (0 : vs)
  where
    vs = do
      s <- maybeToList m ++ [s | (s,_,_) <- cs]
      (_, tm) <- s
      lit <- tm
      return $ abs lit

pbPrintModel :: SAT.Model -> IO ()
pbPrintModel m = do  
  forM_ (split 10 (IM.toList m)) $ \xs -> do
    putStr "v"
    forM_ xs $ \(var,val) -> putStr (" " ++ (if val then "" else "-") ++ "x" ++ show var)
    putStrLn ""
  hFlush stdout

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

addPBAtLeastSoft :: SAT.Solver -> SAT.Lit -> [(Integer,SAT.Lit)] -> Integer -> IO ()
addPBAtLeastSoft solver sel lhs rhs = do
  let (lhs',rhs') = SAT.normalizePBAtLeast (lhs,rhs)
  SAT.addPBAtLeast solver ((rhs', SAT.litNot sel) : lhs') rhs'

addPBAtMostSoft :: SAT.Solver -> SAT.Lit -> [(Integer,SAT.Lit)] -> Integer -> IO ()
addPBAtMostSoft solver sel lhs rhs =
  addPBAtLeastSoft solver sel [(negate c, lit) | (c,lit) <- lhs] (negate rhs)

addPBExactlySoft :: SAT.Solver -> SAT.Lit -> [(Integer,SAT.Lit)] -> Integer -> IO ()
addPBExactlySoft solver sel lhs rhs = do
  addPBAtLeastSoft solver sel lhs rhs
  addPBAtMostSoft solver sel lhs rhs

solveWBO :: Options -> SAT.Solver -> Bool -> PBFile.SoftFormula -> IO ()
solveWBO opt solver isMaxSat formula@(tco, cs) = do
  let nvar = wboNumVars formula
  printf "c #vars %d\n" nvar
  printf "c #constraints %d\n" (length cs)

  _ <- replicateM nvar (SAT.newVar solver)
  lin <- Lin.newLinearizer solver
  Lin.setUsePB lin (optLinearizerPB opt)

  obj <- liftM concat $ forM cs $ \(cost, (lhs, op, rhs)) -> do
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
          PBFile.Ge -> addPBAtLeastSoft solver sel lhs' rhs
          PBFile.Eq -> addPBExactlySoft solver sel lhs' rhs
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
      let m2 = IM.filterWithKey (\v _ -> v <= nvar) m
      if isMaxSat
        then maxsatPrintModel m2
        else pbPrintModel m2
    Left (e :: AsyncException) -> do
      r <- readIORef modelRef
      case r of
        Just m | not isMaxSat -> do
          putStrLn $ "s " ++ "SATISFIABLE"
          let m2 = IM.filterWithKey (\v _ -> v <= nvar) m
          pbPrintModel m2
        _ -> do
          putStrLn $ "s " ++ "UNKNOWN"
          hFlush stdout
      throwIO e

wboNumVars :: PBFile.SoftFormula -> Int
wboNumVars (_, cs) = maximum vs
  where
    vs = do
      s <- [s | (_, (s,_,_)) <- cs]
      (_, tm) <- s
      lit <- tm
      return $ abs lit

-- ------------------------------------------------------------------------

type WeightedClause = (Integer, SAT.Clause)

mainMaxSAT :: Options -> SAT.Solver -> [String] -> IO ()
mainMaxSAT opt solver args = do
  s <- case args of
         ["-"]   -> getContents
         [fname] -> readFile fname
         _ -> showHelp stderr  >> exitFailure
  let (l:ls) = filter (not . isComment) (lines s)
  let wcnf = case words l of
        (["p","wcnf", nvar, _nclause, top]) ->
          (read nvar, read top, map parseWCNFLine ls)
        (["p","wcnf", nvar, _nclause]) ->
          (read nvar, 2^(63::Int), map parseWCNFLine ls)
        (["p","cnf", nvar, _nclause]) ->
          (read nvar, 2, map parseCNFLine ls)
        _ -> error "parse error"
  solveMaxSAT opt solver wcnf

isComment :: String -> Bool
isComment ('c':_) = True
isComment _ = False

parseWCNFLine :: String -> WeightedClause
parseWCNFLine s =
  case map read (words s) of
    (w:xs) ->
        let ys = map fromIntegral $ init xs
        in seq w $ seqList ys $ (w, ys)
    _ -> error "parse error"

parseCNFLine :: String -> WeightedClause
parseCNFLine s = seq xs $ seqList xs $ (1, xs)
  where
    xs = init (map read (words s))

seqList :: [a] -> b -> b
seqList [] b = b
seqList (x:xs) b = seq x $ seqList xs b

solveMaxSAT :: Options -> SAT.Solver -> (Int, Integer, [WeightedClause]) -> IO ()
solveMaxSAT opt solver (_, top, cs) = do
  solveWBO opt solver True
           ( Nothing
           , [ (if w >= top then Nothing else Just w
             , ([(1,[lit]) | lit<-lits], PBFile.Ge, 1))
             | (w,lits) <- cs
             ]
           )

maxsatPrintModel :: SAT.Model -> IO ()
maxsatPrintModel m = do
  forM_ (split 10 (IM.toList m)) $ \xs -> do
    putStr "v"
    forM_ xs $ \(var,val) -> putStr (' ' : show (SAT.literal var val))
    putStrLn ""
  -- no terminating 0 is necessary
  hFlush stdout

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
  if not (Set.null nbvs)
    then do
      hPutStrLn stderr ("cannot handle non-binary variables: " ++ intercalate ", " (Set.toList nbvs))
      exitFailure
    else do
      vmap <- liftM Map.fromList $ forM (Set.toList bvs) $ \v -> do
        v2 <- SAT.newVar solver 
        _ <- printf "c x%d := %s\n" v2 v
        return (v,v2)

      putStrLn "c Loading bounds"
      forM_ (Set.toList (LPFile.variables lp)) $ \var -> do
        let (lb,ub) = LPFile.getBounds lp var
        let var' = vmap Map.! var
        case lb of
          LPFile.NegInf   -> return ()
          LPFile.Finite x -> SAT.addPBAtLeast solver [(1, var')] (ceiling x)
          LPFile.PosInf   -> SAT.addPBAtLeast solver [] 1
        case ub of
          LPFile.NegInf   -> SAT.addPBAtMost solver [] (-1)
          LPFile.Finite x -> SAT.addPBAtMost solver [(1, var')] (ceiling x)
          LPFile.PosInf   -> return ()

      putStrLn "c Loading constraints"
      forM_ (LPFile.constraints lp) $ \(_label, indicator, (lhs, op, rhs)) -> do
        let d = foldl' lcm 1 (map denominator  (rhs:[r | LPFile.Term r _ <- lhs]))
            lhs' = [(asInteger (r * fromIntegral d), vmap Map.! (asSingleton vs)) | LPFile.Term r vs <- lhs]
            rhs' = asInteger (rhs * fromIntegral d)
        case indicator of
          Nothing ->
            case op of
              LPFile.Le  -> SAT.addPBAtMost  solver lhs' rhs'
              LPFile.Ge  -> SAT.addPBAtLeast solver lhs' rhs'
              LPFile.Eql -> SAT.addPBExactly solver lhs' rhs'
          Just (var, val) -> do
            let var' = vmap Map.! var
                f sel = do
                  case op of
                    LPFile.Le  -> addPBAtMostSoft  solver sel lhs' rhs'
                    LPFile.Ge  -> addPBAtLeastSoft solver sel lhs' rhs'
                    LPFile.Eql -> addPBExactlySoft solver sel lhs' rhs'
            case  val of
              1 -> f var'
              0 -> f (SAT.litNot var')
              _ -> return ()

      putStrLn "c Loading SOS constraints"
      forM_ (LPFile.sos lp) $ \(_label, typ, xs) -> do
        case typ of
          LPFile.S1 -> SAT.addAtMost solver (map ((vmap Map.!) . fst) xs) 1
          LPFile.S2 -> do
            let ps = nonAdjacentPairs $ map fst $ sortBy (compare `on` snd) $ xs
            forM_ ps $ \(x1,x2) -> do
              SAT.addClause solver [SAT.litNot (vmap Map.! v) | v <- [x1,x2]]

      let (_label,obj) = LPFile.objectiveFunction lp      
          d = foldl' lcm 1 [denominator r | LPFile.Term r _ <- obj] *
              (if LPFile.dir lp == LPFile.OptMin then 1 else -1)
          obj2 = [(numerator (r * fromIntegral d), vmap Map.! (asSingleton vs)) | LPFile.Term r vs <- obj]

      modelRef <- newIORef Nothing

      result <- try $ minimize opt solver obj2 $ \m val -> do
        writeIORef modelRef (Just m)
        putStrLn $ "o " ++ show (fromIntegral val / fromIntegral d :: Double)
        hFlush stdout

      let printModel :: SAT.Model -> IO ()
          printModel m = do
            forM_ (Set.toList bvs) $ \v -> do
              let val = m IM.! (vmap Map.! v)
              printf "v %s = %s\n" v (if val then "1" else "0")
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
    bvs = LPFile.binaryVariables lp `Set.union` Set.filter p (LPFile.integerVariables lp)
      where
        p v = case LPFile.getBounds lp v of
                (LPFile.Finite lb, LPFile.Finite ub) -> 0 <= lb && ub <= 1
                _ -> False
    nbvs = LPFile.variables lp `Set.difference` bvs

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

-- ------------------------------------------------------------------------

split :: Int -> [a] -> [[a]]
split n = go
  where
    go [] = []
    go xs =
      case splitAt n xs of
        (ys, zs) -> ys : go zs

