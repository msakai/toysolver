-----------------------------------------------------------------------------
-- |
-- Module      :  toysolver
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------


module Main where

import Control.Monad
import Data.Char
import Data.List
import Data.Maybe
import Data.Ratio
import qualified Data.Version as V
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import System.Exit
import System.Environment
import System.FilePath
import System.Console.GetOpt
import System.IO
import Text.Printf
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS

import Data.Expr
import Data.Formula
import qualified Data.LA as LA
import qualified OmegaTest
import qualified Cooper
import qualified MIPSolverHL
import qualified Text.LPFile as LP
import qualified Text.PBFile as PBFile
import qualified Text.MaxSAT as MaxSAT
import qualified Converter.CNF2LP as CNF2LP
import qualified Converter.PB2LP as PB2LP
import qualified Converter.MaxSAT2LP as MaxSAT2LP
import qualified Simplex2
import qualified MIPSolver2
import Version
import Util

-- ---------------------------------------------------------------------------

data Mode = ModeSAT | ModePB | ModeWBO | ModeMaxSAT | ModeLP
  deriving (Eq, Ord)

data Flag
    = Help
    | Version
    | Solver String
    | PrintRational
    | PivotStrategy String
    | NThread !Int
    | Mode !Mode
    deriving Eq

options :: [OptDescr Flag]
options =
    [ Option ['h'] ["help"]    (NoArg Help)            "show help"
    , Option ['v'] ["version"] (NoArg Version)         "show version number"
    , Option [] ["solver"] (ReqArg Solver "SOLVER")    "mip (default), omega-test, cooper, old-mip"
    , Option [] ["print-rational"] (NoArg PrintRational) "print rational numbers instead of decimals"
    , Option [] ["pivot-strategy"] (ReqArg PivotStrategy "[bland-rule|largest-coefficient]") "pivot strategy for simplex (default: bland-rule)"
    , Option [] ["threads"] (ReqArg (NThread . read) "INTEGER") "number of threads to use"

    , Option []    ["sat"]    (NoArg (Mode ModeSAT))    "solve pseudo boolean problems in .cnf file"
    , Option []    ["pb"]     (NoArg (Mode ModePB))     "solve pseudo boolean problems in .pb file"
    , Option []    ["wbo"]    (NoArg (Mode ModeWBO))    "solve weighted boolean optimization problem in .opb file"
    , Option []    ["maxsat"] (NoArg (Mode ModeMaxSAT)) "solve MaxSAT problem in .cnf or .wcnf file"
    , Option []    ["lp"]     (NoArg (Mode ModeLP))     "solve binary integer programming problem in .lp file (default)"
    ]

header :: String
header = "Usage: toysolver [OPTION]... file.lp"

-- ---------------------------------------------------------------------------

run :: String -> [Flag] -> LP.LP -> IO ()
run solver opt lp = do
  unless (Set.null (LP.semiContinuousVariables lp)) $ do
    hPutStrLn stderr "semi-continuous variables are not supported."
    exitFailure  
  case map toLower solver of
    s | s `elem` ["omega-test", "cooper"] -> solveByQE
    s | s `elem` ["old-mip"] -> solveByMIP
    _ -> solveByMIP2
  where
    vs = LP.variables lp
    vsAssoc = zip (Set.toList vs) [0..]
    nameToVar = Map.fromList vsAssoc
    varToName = IM.fromList [(v,name) | (name,v) <- vsAssoc]

    compileE :: LP.Expr -> Expr Rational
    compileE = foldr (+) (Const 0) . map compileT

    compileT :: LP.Term -> Expr Rational
    compileT (LP.Term c vs) =
      foldr (*) (Const c) [Var (nameToVar Map.! v) | v <- vs]

    obj = compileE $ snd $ LP.objectiveFunction lp

    cs1 = do
      v <- Set.toList vs
      let v2 = Var (nameToVar Map.! v)
      let (l,u) = LP.getBounds lp v
      [Const x .<=. v2 | LP.Finite x <- return l] ++
        [v2 .<=. Const x | LP.Finite x <- return u]
    cs2 = do
      LP.Constraint
        { LP.constrIndicator = ind
        , LP.constrBody = (lhs, rel, rhs)
        } <- LP.constraints lp
      let rel2 = case rel of
                  LP.Ge  -> Ge
                  LP.Le  -> Le
                  LP.Eql -> Eql
      case ind of
        Nothing -> return (Rel (compileE lhs) rel2 (Const rhs))
        Just _ -> error "indicator constraint is not supported yet"
    cs3 = do
      v <- Set.toList (LP.binaryVariables lp)
      let v' = nameToVar Map.! v
      [ Const 0 .<=. Var v', Var v' .<=. Const 1 ]

    ivs = f (LP.integerVariables lp) `IS.union` f (LP.binaryVariables lp)
      where
        f = IS.fromList . map (nameToVar Map.!) . Set.toList

    solveByQE =
      case mapM LA.compileAtom (cs1 ++ cs2 ++ cs3) of
        Nothing -> do
          putStrLn "s UNKNOWN"
          exitFailure
        Just cs ->
          case f cs ivs of
            Nothing -> do
              putStrLn "s UNSATISFIABLE"
              exitFailure
            Just m -> do
              putStrLn $ "o " ++ showValue (Data.Expr.eval m obj)
              putStrLn "s SATISFIABLE"
              printModel m vs
       where
         f = case solver of
               "omega-test" -> OmegaTest.solveQFLA
               "cooper"     -> Cooper.solveQFLA
               _ -> error "unknown solver"

    solveByMIP =
      case MIPSolverHL.optimize (LP.dir lp) obj (cs1 ++ cs2 ++ cs3) ivs of
        OptUnknown -> do
          putStrLn "s UNKNOWN"
          exitFailure
        OptUnsat -> do
          putStrLn "s UNSATISFIABLE"
          exitFailure
        Unbounded -> do
          putStrLn "s UNBOUNDED"
          exitFailure
        Optimum r m -> do
          putStrLn $ "o " ++ showValue r
          putStrLn "s OPTIMUM FOUND"
          printModel m vs

    solveByMIP2 = do
      solver <- Simplex2.newSolver

      let ps = last ("bland-rule" : [s | PivotStrategy s <- opt])
      case ps of
        "bland-rule"          -> Simplex2.setPivotStrategy solver Simplex2.PivotStrategyBlandRule
        "largest-coefficient" -> Simplex2.setPivotStrategy solver Simplex2.PivotStrategyLargestCoefficient
        _ -> error ("unknown pivot strategy \"" ++ ps ++ "\"")

      let nthreads = last (0 : [n | NThread n <- opt])

      let logger s = putStr "c " >> putStrLn s >> hFlush stdout

      Simplex2.setLogger solver logger
      replicateM (length vsAssoc) (Simplex2.newVar solver) -- XXX
      Simplex2.setOptDir solver (LP.dir lp)
      Simplex2.setObj solver $ fromJust (LA.compileExpr obj)
      logger "Loading constraints... "
      forM_ (cs1 ++ cs2 ++ cs3) $ \c -> do
        Simplex2.assertAtom solver $ fromJust (LA.compileAtom c)
      logger "Loading constraints finished"

      mip <- MIPSolver2.newSolver solver ivs
      MIPSolver2.setShowRational mip printRat
      MIPSolver2.setLogger mip logger
      MIPSolver2.setNThread mip nthreads
      let update m val = do
            putStrLn $ "o " ++ showValue val
      ret <- MIPSolver2.optimize mip update
      case ret of
        Simplex2.Unsat -> do
          putStrLn "s UNSATISFIABLE"
          exitFailure
        Simplex2.Unbounded -> do
          putStrLn "s UNBOUNDED"
          exitFailure
        Simplex2.Optimum -> do
          m <- MIPSolver2.model mip
          r <- MIPSolver2.getObjValue mip
          putStrLn "s OPTIMUM FOUND"
          printModel m vs

    printModel :: Model Rational -> Set.Set String -> IO ()
    printModel m vs =
      forM_ (Set.toList vs) $ \v -> do
        printf "v %s = %s\n" v (showValue (m IM.! (nameToVar Map.! v)))

    printRat :: Bool
    printRat = PrintRational `elem` opt

    showValue :: Rational -> String
    showValue = showRational printRat

-- ---------------------------------------------------------------------------

getSolver :: [Flag] -> String
getSolver xs = last $ "mip" : [s | Solver s <- xs]

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (o,_,[])
      | Help `elem` o    -> putStrLn (usageInfo header options)
      | Version `elem` o -> putStrLn (V.showVersion version)
    (o,[fname],[]) -> do

      let mode =
            case reverse [m | Mode m <- o] of
              m:_ -> m
              [] ->
                case map toLower (takeExtension fname) of
                  ".cnf"  -> ModeSAT
                  ".opb"  -> ModePB
                  ".wbo"  -> ModeWBO
                  ".wcnf" -> ModeMaxSAT
                  ".lp"   -> ModeLP
                  _ -> ModeLP

      case mode of
        ModeSAT -> do
          ret <- DIMACS.parseFile fname
          case ret of
            Left err -> hPrint stderr err >> exitFailure
            Right cnf -> do
              let (lp,mtrans) = CNF2LP.convert CNF2LP.ObjNone cnf
              run (getSolver o) o lp
        ModePB -> do
          ret <- PBFile.parseOPBFile fname
          case ret of
            Left err -> hPrint stderr err >> exitFailure
            Right pb -> do
              let (lp,mtrans) = PB2LP.convert PB2LP.ObjNone pb
              run (getSolver o) o lp
        ModeWBO -> do
          ret <- PBFile.parseWBOFile fname
          case ret of
            Left err -> hPrint stderr err >> exitFailure
            Right wbo -> do
              let (lp,mtrans) = PB2LP.convertWBO False wbo
              run (getSolver o) o lp
        ModeMaxSAT -> do
          wcnf <- MaxSAT.parseWCNFFile fname
          let (lp,mtrans) = MaxSAT2LP.convert wcnf
          run (getSolver o) o lp
        ModeLP -> do
          ret <- LP.parseFile fname
          case ret of
            Left err -> hPrint stderr err >> exitFailure
            Right lp -> run (getSolver o) o lp
    (_,_,errs) ->
        hPutStrLn stderr $ concat errs ++ usageInfo header options
