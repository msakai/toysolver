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
import Data.Array.IArray
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
import Data.ArithRel
import Data.Formula (Atom (..))
import Data.OptDir
import qualified Data.LA as LA
import qualified Data.Polynomial as P
import qualified Data.AlgebraicNumber as AReal
import qualified OmegaTest
import qualified Cooper
import qualified MIPSolverHL
import qualified Text.LPFile as LP
import qualified Text.PBFile as PBFile
import qualified Text.MaxSAT as MaxSAT
import qualified Text.GurobiSol as GurobiSol
import qualified Converter.CNF2LP as CNF2LP
import qualified Converter.PB2LP as PB2LP
import qualified Converter.MaxSAT2LP as MaxSAT2LP
import qualified Simplex2
import qualified MIPSolver2
import qualified CAD
import qualified ContiTraverso
import SAT.Printer
import qualified SAT.Types as SAT
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
    | WriteFile !FilePath
    | NoMIP
    | PivotStrategy String
    | NThread !Int
    | Mode !Mode
    deriving Eq

options :: [OptDescr Flag]
options =
    [ Option ['h'] ["help"]    (NoArg Help)            "show help"
    , Option ['v'] ["version"] (NoArg Version)         "show version number"
    , Option [] ["solver"] (ReqArg Solver "SOLVER")    "mip (default), omega-test, cooper, cad, old-mip, ct"
    , Option [] ["print-rational"] (NoArg PrintRational) "print rational numbers instead of decimals"
    , Option ['w'] [] (ReqArg WriteFile "<filename>")  "write solution to filename in Gurobi .sol format"

    , Option [] ["print-rational"] (NoArg PrintRational) "print rational numbers instead of decimals"

    , Option [] ["pivot-strategy"] (ReqArg PivotStrategy "[bland-rule|largest-coefficient]") "pivot strategy for simplex (default: bland-rule)"
    , Option [] ["threads"] (ReqArg (NThread . read) "INTEGER") "number of threads to use"

    , Option []    ["sat"]    (NoArg (Mode ModeSAT))    "solve boolean satisfiability problems in .cnf file"
    , Option []    ["pb"]     (NoArg (Mode ModePB))     "solve pseudo boolean problems in .pb file"
    , Option []    ["wbo"]    (NoArg (Mode ModeWBO))    "solve weighted boolean optimization problem in .opb file"
    , Option []    ["maxsat"] (NoArg (Mode ModeMaxSAT)) "solve MaxSAT problem in .cnf or .wcnf file"
    , Option []    ["lp"]     (NoArg (Mode ModeLP))     "solve binary integer programming problem in .lp file (default)"

    , Option [] ["nomip"] (NoArg NoMIP)                 "consider all integer variables as continuous"
    ]

header :: String
header = "Usage: toysolver [OPTION]... file.lp"

-- ---------------------------------------------------------------------------

run
  :: String
  -> [Flag]
  -> LP.LP
  -> (Map.Map String Rational -> IO ())
  -> IO ()
run solver opt lp printModel = do
  unless (Set.null (LP.semiContinuousVariables lp)) $ do
    hPutStrLn stderr "semi-continuous variables are not supported."
    exitFailure  
  case map toLower solver of
    s | s `elem` ["omega", "omega-test", "cooper"] -> solveByQE
    s | s `elem` ["old-mip"] -> solveByMIP
    s | s `elem` ["cad"] -> solveByCAD
    s | s `elem` ["ct", "conti-traverso"] -> solveByContiTraverso
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

    ivs
      | NoMIP `elem` opt = Set.empty
      | otherwise        = LP.integerVariables lp `Set.union` LP.binaryVariables lp

    ivs2 = IS.fromList . map (nameToVar Map.!) . Set.toList $ ivs

    solveByQE =
      case mapM LA.compileAtom (cs1 ++ cs2 ++ cs3) of
        Nothing -> do
          putStrLn "s UNKNOWN"
          exitFailure
        Just cs ->
          case f cs ivs2 of
            Nothing -> do
              putStrLn "s UNSATISFIABLE"
              exitFailure
            Just m -> do
              putStrLn $ "o " ++ showValue (Data.Expr.eval m obj)
              putStrLn "s SATISFIABLE"
              let m2 = Map.fromAscList [(v, m IM.! (nameToVar Map.! v)) | v <- Set.toList vs]
              printModel m2
       where
         f = case solver of
               "omega"      -> OmegaTest.solveQFLA
               "omega-test" -> OmegaTest.solveQFLA
               "cooper"     -> Cooper.solveQFLA
               _ -> error "unknown solver"

    solveByMIP =
      case MIPSolverHL.optimize (LP.dir lp) obj (cs1 ++ cs2 ++ cs3) ivs2 of
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
          let m2 = Map.fromAscList [(v, m IM.! (nameToVar Map.! v)) | v <- Set.toList vs]
          printModel m2

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

      mip <- MIPSolver2.newSolver solver ivs2
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
          m <- MIPSolver2.model mip
          let m2 = Map.fromAscList [(v, m IM.! (nameToVar Map.! v)) | v <- Set.toList vs]
          printModel m2
          exitFailure
        Simplex2.Optimum -> do
          m <- MIPSolver2.model mip
          r <- MIPSolver2.getObjValue mip
          putStrLn "s OPTIMUM FOUND"
          let m2 = Map.fromAscList [(v, m IM.! (nameToVar Map.! v)) | v <- Set.toList vs]
          printModel m2

    solveByCAD
      | not (IS.null ivs2) = do
          putStrLn "s UNKNOWN"
          putStrLn "c integer variables are not supported by CAD"
          exitFailure
      | otherwise = do
          let cs = map g $ cs1 ++ cs2 ++ cs3
          case CAD.solve cs of
            Nothing -> do
              putStrLn "s UNSATISFIABLE"
              exitFailure
            Just m -> do
              let m2 = IM.map (\x -> AReal.approx x (2^^(-64::Int))) $
                         IM.fromAscList $ Map.toAscList $ m
              putStrLn $ "o " ++ showValue (Data.Expr.eval m2 obj)
              putStrLn "s SATISFIABLE"
              let m3 = Map.fromAscList [(v, m2 IM.! (nameToVar Map.! v)) | v <- Set.toList vs]
              printModel m3
      where
        g (Rel lhs rel rhs) = Rel (f lhs) rel (f rhs)

        f (Const r)   = P.constant r
        f (Var v)     = P.var v
        f (e1 :+: e2) = f e1 + f e2
        f (e1 :*: e2) = f e1 * f e2
        f (e1 :/: e2)
          | P.deg p > 0 = error "can't handle rational expression"
          | otherwise   = P.mapCoeff (/ c) $ f e1 
          where
            p = f e2
            c = P.coeff P.mmOne p

    solveByContiTraverso
      | not (vs `Set.isSubsetOf` ivs) = do
          putStrLn "s UNKNOWN"
          putStrLn "c continuous variables are not supported by Conti-Traverso algorithm"
          exitFailure
      | otherwise = do
          let tmp = do
                linObj <- LA.compileExpr obj
                linCon <- mapM LA.compileAtom (cs1 ++ cs2 ++ cs3)
                return (linObj, linCon)
          case tmp of
            Nothing -> do
              putStrLn "s UNKNOWN"
              putStrLn "c non-linear expressions are not supported by Conti-Traverso algorithm"
              exitFailure
            Just (linObj, linCon) -> do
              case ContiTraverso.solve P.grlex (LP.dir lp) linObj linCon of
                Nothing -> do
                  putStrLn "s UNSATISFIABLE"
                  exitFailure
                Just m -> do
                  let m2 = IM.map fromInteger m
                  putStrLn $ "o " ++ showValue (Data.Expr.eval m2 obj)
                  putStrLn "s OPTIMUM FOUND"
                  let m3 = Map.fromAscList [(v, m2 IM.! (nameToVar Map.! v)) | v <- Set.toList vs]
                  printModel m3

    printRat :: Bool
    printRat = PrintRational `elem` opt

    showValue :: Rational -> String
    showValue = showRational printRat

lpPrintModel :: Handle -> Bool -> Map.Map String Rational -> IO ()
lpPrintModel h asRat m = do
  forM_ (Map.toList m) $ \(v, val) -> do
    printf "v %s = %s\n" v (showRational asRat val)

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
              run (getSolver o) o lp $ \m -> do
                let m2 = mtrans m
                satPrintModel stdout m2 0
                writeSOLFileSAT o m2
        ModePB -> do
          ret <- PBFile.parseOPBFile fname
          case ret of
            Left err -> hPrint stderr err >> exitFailure
            Right pb -> do
              let (lp,mtrans) = PB2LP.convert PB2LP.ObjNone pb
              run (getSolver o) o lp $ \m -> do
                let m2 = mtrans m
                pbPrintModel stdout m2 0
                writeSOLFileSAT o m2
        ModeWBO -> do
          ret <- PBFile.parseWBOFile fname
          case ret of
            Left err -> hPrint stderr err >> exitFailure
            Right wbo -> do
              let (lp,mtrans) = PB2LP.convertWBO False wbo
              run (getSolver o) o lp $ \m -> do
                let m2 = mtrans m
                pbPrintModel stdout m2 0
                writeSOLFileSAT o m2
        ModeMaxSAT -> do
          wcnf <- MaxSAT.parseWCNFFile fname
          let (lp,mtrans) = MaxSAT2LP.convert wcnf
          run (getSolver o) o lp $ \m -> do
            let m2 = mtrans m
            maxsatPrintModel stdout m2 0
            writeSOLFileSAT o m2
        ModeLP -> do
          ret <- LP.parseFile fname
          case ret of
            Left err -> hPrint stderr err >> exitFailure
            Right lp -> do
              run (getSolver o) o lp $ \m -> do
                lpPrintModel stdout (PrintRational `elem` o) m
                writeSOLFileLP o m
    (_,_,errs) ->
        hPutStrLn stderr $ concat errs ++ usageInfo header options

-- FIXME: 目的関数値を表示するように
writeSOLFileLP :: [Flag] -> Map.Map String Rational -> IO ()
writeSOLFileLP opt m = do
  forM_ [fname | WriteFile fname <- opt ] $ \fname -> do
    let m2 = Map.map fromRational m
    writeFile fname (GurobiSol.render m2 Nothing)

-- FIXME: 目的関数値を表示するように
writeSOLFileSAT :: [Flag] -> SAT.Model -> IO ()
writeSOLFileSAT opt m = do
  let m2 = Map.fromList [("x" ++ show x, if b then 1 else 0) | (x,b) <- assocs m]
  writeSOLFileLP opt m2
