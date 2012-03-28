{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  toysat
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- A toy-level SAT solver based on CDCL.
--
-----------------------------------------------------------------------------

module Main where

import Control.Monad
import Data.Array.IArray
import qualified Data.ByteString.Lazy as BS
import qualified Data.IntMap as IM
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Char
import Data.Function
import Data.List
import Data.Maybe
import Data.Ratio
import Data.Version
import System.IO
import System.Environment
import System.Exit
import System.Console.GetOpt
import qualified System.Info as SysInfo
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS
import Text.Printf
import qualified SAT
import qualified PBFile
import qualified LPFile

-- ------------------------------------------------------------------------

data Mode = ModeHelp | ModeSAT | ModePB | ModeWBO | ModeMaxSAT | ModeLP

data Options
  = Options
  { optMode          :: Mode
  , optRestartFirst  :: Int
  , optRestartInc    :: Double
  , optLearntSizeInc :: Double
  }

defaultOptions :: Options
defaultOptions
  = Options
  { optMode          = ModeSAT
  , optRestartFirst  = SAT.defaultRestartFirst
  , optRestartInc    = SAT.defaultRestartInc
  , optLearntSizeInc = SAT.defaultLearntSizeInc
  }

options :: [OptDescr (Options -> Options)]
options =
    [ Option ['h'] ["help"]   (NoArg (\opt -> opt{ optMode = ModeHelp   })) "show help"
    , Option []    ["pb"]     (NoArg (\opt -> opt{ optMode = ModePB     })) "solve pseudo boolean problems in .pb file"
    , Option []    ["wbo"]    (NoArg (\opt -> opt{ optMode = ModeWBO    })) "solve weighted boolean optimization problem in .opb file"
    , Option []    ["maxsat"] (NoArg (\opt -> opt{ optMode = ModeMaxSAT })) "solve MaxSAT problem in .cnf or .wcnf file"
    , Option []    ["lp"]     (NoArg (\opt -> opt{ optMode = ModeLP     })) "solve binary integer programming problem in .lp file"

    , Option [] ["restart-first"]
        (ReqArg (\val opt -> opt{ optRestartFirst = read val }) "<integer>")
        (printf "The initial restart limit. (default %d)" SAT.defaultRestartFirst)
    , Option [] ["restart-inc"]
        (ReqArg (\val opt -> opt{ optRestartInc = read val }) "<real>")
        (printf "The factor with which the restart limit is multiplied in each restart. (default %f)" SAT.defaultRestartInc)
    , Option [] ["learnt-size-inc"]
        (ReqArg (\val opt -> opt{ optLearntSizeInc = read val }) "<real>")
        (printf "The limit for learnt clauses is multiplied with this factor each restart. (default %f)" SAT.defaultLearntSizeInc)

    ]

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (o,args2,[]) -> do
      let opt = foldl (flip id) defaultOptions o
      solver <- newSolver opt
      case optMode opt of
        ModeHelp   -> showHelp stdout
        ModeSAT    -> mainSAT solver args2
        ModePB     -> mainPB solver args2
        ModeWBO    -> mainWBO solver args2
        ModeMaxSAT -> mainMaxSAT solver args2
        ModeLP     -> mainLP solver args2
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
  hPrintf stdout "c arch = %s\n" SysInfo.arch
  hPrintf stdout "c os = %s\n" SysInfo.os
  hPrintf stdout "c compiler = %s %s\n" SysInfo.compilerName (showVersion SysInfo.compilerVersion)

newSolver :: Options -> IO SAT.Solver
newSolver opts = do
  solver <- SAT.newSolver
  SAT.setRestartFirst  solver (optRestartFirst opts)
  SAT.setRestartInc    solver (optRestartInc opts)
  SAT.setLearntSizeInc solver (optLearntSizeInc opts)
  return solver

-- ------------------------------------------------------------------------

mainSAT :: SAT.Solver -> [String] -> IO ()
mainSAT solver args = do
  ret <- case args of
           ["-"]   -> fmap (DIMACS.parseByteString "-") $ BS.hGetContents stdin
           [fname] -> DIMACS.parseFile fname
           _ -> showHelp stderr >> exitFailure
  case ret of
    Left err -> hPrint stderr err >> exitFailure
    Right cnf -> printSysInfo >> solveCNF solver cnf

solveCNF :: SAT.Solver -> DIMACS.CNF -> IO ()
solveCNF solver cnf = do
  _ <- replicateM (DIMACS.numVars cnf) (SAT.newVar solver)
  forM_ (DIMACS.clauses cnf) $ \clause ->
    SAT.addClause solver (elems clause)
  result <- SAT.solve solver
  putStrLn $ "s " ++ (if result then "SATISFIABLE" else "UNSATISFIABLE")
  hFlush stdout
  when result $ do
    m <- SAT.model solver
    forM_ (IM.toList m) $ \(var,val) ->
      putStrLn ("v " ++ show (SAT.literal var val))
    putStrLn "v 0"
    hFlush stdout

-- ------------------------------------------------------------------------

mainPB :: SAT.Solver -> [String] -> IO ()
mainPB solver args = do
  ret <- case args of
           ["-"]   -> fmap (PBFile.parseOPBString "-") $ hGetContents stdin
           [fname] -> PBFile.parseOPBFile fname
           _ -> showHelp stderr >> exitFailure
  case ret of
    Left err -> hPrint stderr err >> exitFailure
    Right formula -> printSysInfo >> solvePB solver formula

solvePB :: SAT.Solver -> PBFile.Formula -> IO ()
solvePB solver formula@(obj, cs) = do
  let n = pbNumVars formula
  _ <- replicateM n (SAT.newVar solver)
  forM_ cs $ \(lhs, op, rhs) -> do
    let lhs' = pbConvSum lhs
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
        pbPrintModel m

    Just obj' -> do
      result <- minimize solver (pbConvSum obj') $ \val -> do
        putStrLn $ "o " ++ show val
        hFlush stdout
      case result of
        Nothing -> do
          putStrLn $ "s " ++ "UNSATISFIABLE"
          hFlush stdout
        Just m -> do
          putStrLn $ "s " ++ "OPTIMUM FOUND"
          hFlush stdout          
          pbPrintModel m

pbConvSum :: PBFile.Sum -> [(Integer, SAT.Lit)]
pbConvSum = map f
  where
    f (w,[lit]) = (w,lit)
    f _ = error "non-linear terms are not supported"

minimize :: SAT.Solver -> [(Integer, SAT.Lit)] -> (Integer -> IO ()) -> IO (Maybe SAT.Model)
minimize solver obj update = do
  result <- SAT.solve solver
  if result
    then liftM Just loop
    else return Nothing
  where
   loop :: IO SAT.Model
   loop = do
     m <- SAT.model solver
     let v = pbEval m obj
     update v
     SAT.addPBAtMost solver obj (v - 1)
     result <- SAT.solve solver
     if result
       then loop
       else return m

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
  forM_ (IM.toList m) $ \(var,val) ->
    putStrLn ("v " ++ (if val then "" else "-") ++ "x" ++ show var)
  hFlush stdout

-- ------------------------------------------------------------------------

mainWBO :: SAT.Solver -> [String] -> IO ()
mainWBO solver args = do
  ret <- case args of
           ["-"]   -> fmap (PBFile.parseWBOString "-") $ hGetContents stdin
           [fname] -> PBFile.parseWBOFile fname
           _ -> showHelp stderr >> exitFailure
  case ret of
    Left err -> hPrint stderr err >> exitFailure
    Right formula -> printSysInfo >> solveWBO solver False formula

wboAddAtLeast :: SAT.Solver -> SAT.Lit -> [(Integer,SAT.Lit)] -> Integer -> IO ()
wboAddAtLeast solver sel lhs rhs = do
  let (lhs',rhs') = SAT.normalizePBAtLeast (lhs,rhs)
  SAT.addPBAtLeast solver ((rhs', SAT.litNot sel) : lhs') rhs'

wboAddAtMost :: SAT.Solver -> SAT.Lit -> [(Integer,SAT.Lit)] -> Integer -> IO ()
wboAddAtMost solver sel lhs rhs =
  wboAddAtLeast solver sel [(negate c, lit) | (c,lit) <- lhs] (negate rhs)

wboAddExactly :: SAT.Solver -> SAT.Lit -> [(Integer,SAT.Lit)] -> Integer -> IO ()
wboAddExactly solver sel lhs rhs = do
  wboAddAtLeast solver sel lhs rhs
  wboAddAtMost solver sel lhs rhs

solveWBO :: SAT.Solver -> Bool -> PBFile.SoftFormula -> IO ()
solveWBO solver isMaxSat formula@(tco, cs) = do
  let nvar = wboNumVars formula
  _ <- replicateM nvar (SAT.newVar solver)

  obj <- liftM concat $ forM cs $ \(cost, (lhs, op, rhs)) -> do
    let lhs' = pbConvSum lhs
    case cost of
      Nothing -> do
        case op of
          PBFile.Ge -> SAT.addPBAtLeast solver lhs' rhs
          PBFile.Eq -> SAT.addPBExactly solver lhs' rhs
        return []
      Just cost -> do
        sel <- SAT.newVar solver
        case op of
          PBFile.Ge -> wboAddAtLeast solver sel lhs' rhs
          PBFile.Eq -> wboAddExactly solver sel lhs' rhs
        return [(cost, SAT.litNot sel)]

  case tco of
    Nothing -> return ()
    Just c -> SAT.addPBAtMost solver obj (c-1)

  result <- minimize solver obj $ \val -> do
     putStrLn $ "o " ++ show val
     hFlush stdout
  case result of
    Nothing -> do
      putStrLn $ "s " ++ "UNSATISFIABLE"
      hFlush stdout
    Just m -> do
      putStrLn $ "s " ++ "OPTIMUM FOUND"
      hFlush stdout
      let m2 = IM.filterWithKey (\v _ -> v <= nvar) m
      if isMaxSat
        then maxsatPrintModel m2
        else pbPrintModel m2

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

mainMaxSAT :: SAT.Solver -> [String] -> IO ()
mainMaxSAT solver args = do
  s <- case args of
         ["-"]   -> getContents
         [fname] -> readFile fname
         _ -> showHelp stderr  >> exitFailure
  let (l:ls) = filter (not . isComment) (lines s)
  let wcnf = case words l of
        (["p","wcnf", nvar, nclause, top]) ->
          (read nvar, read top, map parseWCNFLine ls)
        (["p","wcnf", nvar, nclause]) ->
          (read nvar, 2^(63::Int), map parseWCNFLine ls)
        (["p","cnf", nvar, nclause]) ->
          (read nvar, 2, map parseCNFLine ls)
        _ -> error "parse error"
  printSysInfo >> solveMaxSAT solver wcnf

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

solveMaxSAT :: SAT.Solver -> (Int, Integer, [WeightedClause]) -> IO ()
solveMaxSAT solver (_, top, cs) = do
  solveWBO solver True
           ( Nothing
           , [ (if w >= top then Nothing else Just w
             , ([(1,[lit]) | lit<-lits], PBFile.Ge, 1))
             | (w,lits) <- cs
             ]
           )

maxsatPrintModel :: SAT.Model -> IO ()
maxsatPrintModel m = do
  forM_ (IM.toList m) $ \(var,val) ->
    putStrLn ("v " ++ show (SAT.literal var val))
  -- no terminating 0 is necessary
  hFlush stdout

-- ------------------------------------------------------------------------

mainLP :: SAT.Solver -> [String] -> IO ()
mainLP solver args = do
  ret <- case args of
           ["-"]   -> fmap (LPFile.parseString "-") $ hGetContents stdin
           [fname] -> LPFile.parseFile fname
           _ -> showHelp stderr >> exitFailure
  case ret of
    Left err -> hPrint stderr err >> exitFailure
    Right lp -> printSysInfo >> solveLP solver lp

solveLP :: SAT.Solver -> LPFile.LP -> IO ()
solveLP solver lp = do
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
      forM_ (LPFile.constraints lp) $ \(label, indicator, (lhs, op, rhs)) -> do
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
                    LPFile.Le  -> wboAddAtMost  solver sel lhs' rhs'
                    LPFile.Ge  -> wboAddAtLeast solver sel lhs' rhs'
                    LPFile.Eql -> wboAddExactly solver sel lhs' rhs'
            case  val of
              1 -> f var'
              0 -> f (SAT.litNot var')
              _ -> return ()

      putStrLn "c Loading SOS constraints"
      forM_ (LPFile.sos lp) $ \(label, typ, xs) -> do
        case typ of
          LPFile.S1 -> SAT.addAtMost solver (map ((vmap Map.!) . fst) xs) 1
          LPFile.S2 -> do
            let ps = nonAdjacentPairs $ map fst $ sortBy (compare `on` snd) $ xs
            forM_ ps $ \(x1,x2) -> do
              SAT.addClause solver [SAT.litNot (vmap Map.! x1) | v <- [x1,x2]]

      let (label,obj) = LPFile.objectiveFunction lp      
          d = foldl' lcm 1 [denominator r | LPFile.Term r _ <- obj] *
              (if LPFile.dir lp == LPFile.OptMin then 1 else -1)
          obj2 = [(numerator (r * fromIntegral d), vmap Map.! (asSingleton vs)) | LPFile.Term r vs <- obj]

      result <- minimize solver obj2 $ \val -> do
        putStrLn $ "o " ++ show (fromIntegral val / fromIntegral d :: Double)
        hFlush stdout

      case result of
        Nothing -> do
          putStrLn $ "s " ++ "UNSATISFIABLE"
          hFlush stdout
        Just m -> do
          putStrLn $ "s " ++ "OPTIMUM FOUND"
          hFlush stdout
          
          forM_ (Set.toList bvs) $ \v -> do
            let val = m IM.! (vmap Map.! v)
            printf "v %s = %s\n" v (if val then "1" else "0")
          hFlush stdout
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
