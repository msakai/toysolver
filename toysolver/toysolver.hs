-----------------------------------------------------------------------------
-- |
-- Module      :  toysolver
-- Copyright   :  (c) Masahiro Sakai 2011-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------


module Main where

import Control.Monad
import Control.Concurrent
import Data.Array.IArray
import Data.Char
import Data.Default.Class
import Data.List
import Data.Maybe
import Data.Ratio
import qualified Data.Version as V
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import System.Exit
import System.Environment
import System.FilePath
import System.Console.GetOpt
import System.IO
import Text.Printf
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS
import GHC.Conc (getNumProcessors, setNumCapabilities)

import Data.OptDir
import qualified Data.PseudoBoolean as PBFile
import qualified Data.PseudoBoolean.Attoparsec as PBFileAttoparsec

import ToySolver.Data.ArithRel
import ToySolver.Data.FOL.Arith as FOL
import qualified ToySolver.Data.LA as LA
import qualified ToySolver.Data.LA.FOL as LAFOL
import qualified ToySolver.Data.Polynomial as P
import qualified ToySolver.Data.AlgebraicNumber.Real as AReal
import qualified ToySolver.Data.MIP as MIP
import qualified ToySolver.Arith.OmegaTest as OmegaTest
import qualified ToySolver.Arith.Cooper as Cooper
import qualified ToySolver.Arith.MIPSolverHL as MIPSolverHL
import qualified ToySolver.Arith.Simplex2 as Simplex2
import qualified ToySolver.Arith.MIPSolver2 as MIPSolver2
import qualified ToySolver.Arith.CAD as CAD
import qualified ToySolver.Arith.ContiTraverso as ContiTraverso
import qualified ToySolver.Text.MaxSAT as MaxSAT
import qualified ToySolver.Text.GurobiSol as GurobiSol
import qualified ToySolver.Converter.SAT2IP as SAT2IP
import qualified ToySolver.Converter.PB2IP as PB2IP
import qualified ToySolver.Converter.MaxSAT2IP as MaxSAT2IP
import ToySolver.SAT.Printer
import qualified ToySolver.SAT.Types as SAT
import ToySolver.Version
import ToySolver.Internal.Util

-- ---------------------------------------------------------------------------

data Mode = ModeSAT | ModePB | ModeWBO | ModeMaxSAT | ModeMIP
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
    | OmegaReal String
    | Mode !Mode
    deriving Eq

options :: [OptDescr Flag]
options =
    [ Option ['h'] ["help"]    (NoArg Help)            "show help"
    , Option ['v'] ["version"] (NoArg Version)         "show version number"
    , Option [] ["solver"] (ReqArg Solver "SOLVER")    "mip (default), omega-test, cooper, cad, old-mip, ct"
    , Option [] ["print-rational"] (NoArg PrintRational) "print rational numbers instead of decimals"
    , Option ['w'] [] (ReqArg WriteFile "<filename>")  "write solution to filename in Gurobi .sol format"

    , Option [] ["pivot-strategy"] (ReqArg PivotStrategy "[bland-rule|largest-coefficient]") "pivot strategy for simplex (default: bland-rule)"
    , Option [] ["threads"] (ReqArg (NThread . read) "INTEGER") "number of threads to use"

    , Option [] ["omega-real"] (ReqArg OmegaReal "SOLVER") "fourier-motzkin (default), virtual-substitution (or vs), cad, simplex, none"

    , Option []    ["sat"]    (NoArg (Mode ModeSAT))    "solve boolean satisfiability problem in .cnf file"
    , Option []    ["pb"]     (NoArg (Mode ModePB))     "solve pseudo boolean problem in .opb file"
    , Option []    ["wbo"]    (NoArg (Mode ModeWBO))    "solve weighted boolean optimization problem in .wbo file"
    , Option []    ["maxsat"] (NoArg (Mode ModeMaxSAT)) "solve MaxSAT problem in .cnf or .wcnf file"
    , Option []    ["lp"]     (NoArg (Mode ModeMIP))    "solve LP/MIP problem in .lp or .mps file (default)"

    , Option [] ["nomip"] (NoArg NoMIP)                 "consider all integer variables as continuous"
    ]

header :: String
header = "Usage: toysolver [OPTION]... file"

-- ---------------------------------------------------------------------------

run
  :: String
  -> [Flag]
  -> MIP.Problem
  -> (Map MIP.Var Rational -> IO ())
  -> IO ()
run solver opt mip printModel = do
  unless (Set.null (MIP.semiContinuousVariables mip)) $ do
    hPutStrLn stderr "semi-continuous variables are not supported."
    exitFailure  
  case map toLower solver of
    s | s `elem` ["omega", "omega-test", "cooper"] -> solveByQE
    s | s `elem` ["old-mip"] -> solveByMIP
    s | s `elem` ["cad"] -> solveByCAD
    s | s `elem` ["ct", "conti-traverso"] -> solveByContiTraverso
    _ -> solveByMIP2
  where
    vs = MIP.variables mip
    vsAssoc = zip (Set.toList vs) [0..]
    nameToVar = Map.fromList vsAssoc
    varToName = IntMap.fromList [(v,name) | (name,v) <- vsAssoc]

    compileE :: MIP.Expr -> Expr Rational
    compileE = foldr (+) (Const 0) . map compileT . MIP.terms

    compileT :: MIP.Term -> Expr Rational
    compileT (MIP.Term c vs) =
      foldr (*) (Const c) [Var (nameToVar Map.! v) | v <- vs]

    obj = compileE $ MIP.objExpr $ MIP.objectiveFunction mip

    cs1 = do
      v <- Set.toList vs
      let v2 = Var (nameToVar Map.! v)
      let (l,u) = MIP.getBounds mip v
      [Const x .<=. v2 | MIP.Finite x <- return l] ++
        [v2 .<=. Const x | MIP.Finite x <- return u]
    cs2 = do
      MIP.Constraint
        { MIP.constrIndicator = ind
        , MIP.constrExpr = e
        , MIP.constrLB = lb
        , MIP.constrUB = ub
        } <- MIP.constraints mip
      case ind of
        Nothing -> do
          let e2 = compileE e
          msum
            [ case lb of
                MIP.NegInf -> []
                MIP.PosInf -> [ArithRel 1 Le 0] -- False
                MIP.Finite x -> [ArithRel e2 Ge (Const x)]
            , case ub of
                MIP.NegInf -> [ArithRel 1 Le 0] -- False
                MIP.PosInf -> []
                MIP.Finite x -> [ArithRel e2 Le (Const x)]
            ]
        Just _ -> error "indicator constraint is not supported yet"

    ivs
      | NoMIP `elem` opt = Set.empty
      | otherwise        = MIP.integerVariables mip

    vs2  = IntMap.keysSet varToName
    ivs2 = IntSet.fromList . map (nameToVar Map.!) . Set.toList $ ivs

    solveByQE =
      case mapM LAFOL.fromFOLAtom (cs1 ++ cs2) of
        Nothing -> do
          putSLine "UNKNOWN"
          exitFailure
        Just cs ->
          case f vs2 cs ivs2 of
            Nothing -> do
              putSLine "UNSATISFIABLE"
              exitFailure
            Just m -> do
              putOLine $ showValue (FOL.evalExpr m obj)
              putSLine "SATISFIABLE"
              let m2 = Map.fromAscList [(v, m IntMap.! (nameToVar Map.! v)) | v <- Set.toList vs]
              printModel m2
       where
         f = case solver of
               "omega"      -> OmegaTest.solveQFLIRAConj omegaOpt
               "omega-test" -> OmegaTest.solveQFLIRAConj omegaOpt
               "cooper"     -> Cooper.solveQFLIRAConj
               _ -> error "unknown solver"

         omegaOpt =
           def
           { OmegaTest.optCheckReal = realSolver
           }         
           where
             realSolver =
               case last ("fourier-motzkin" : [s | OmegaReal s <- opt]) of
                 "fourier-motzkin" -> OmegaTest.checkRealByFM
                 "virtual-substitution" -> OmegaTest.checkRealByVS
                 "vs"              -> OmegaTest.checkRealByVS
                 "cad"             -> OmegaTest.checkRealByCAD
                 "simplex"         -> OmegaTest.checkRealBySimplex
                 "none"            -> OmegaTest.checkRealNoCheck
                 s                 -> error ("unknown solver: " ++ s)

    solveByMIP = do
      let m = do
            cs'  <- mapM LAFOL.fromFOLAtom (cs1 ++ cs2)
            obj' <- LAFOL.fromFOLExpr obj
            return (cs',obj')
      case m of
        Nothing -> do
          putSLine "UNKNOWN"
          exitFailure
        Just (cs',obj') ->
          case MIPSolverHL.optimize (MIP.objDir $ MIP.objectiveFunction mip) obj' cs' ivs2 of
            MIPSolverHL.OptUnsat -> do
              putSLine "UNSATISFIABLE"
              exitFailure
            MIPSolverHL.Unbounded -> do
              putSLine "UNBOUNDED"
              exitFailure
            MIPSolverHL.Optimum r m -> do
              putOLine $ showValue r
              putSLine "OPTIMUM FOUND"
              let m2 = Map.fromAscList [(v, m IntMap.! (nameToVar Map.! v)) | v <- Set.toList vs]
              printModel m2

    solveByMIP2 = do
      solver <- Simplex2.newSolver

      let ps = last ("bland-rule" : [s | PivotStrategy s <- opt])
      case ps of
        "bland-rule"          -> Simplex2.setPivotStrategy solver Simplex2.PivotStrategyBlandRule
        "largest-coefficient" -> Simplex2.setPivotStrategy solver Simplex2.PivotStrategyLargestCoefficient
        _ -> error ("unknown pivot strategy \"" ++ ps ++ "\"")

      let nthreads = last (0 : [n | NThread n <- opt])

      Simplex2.setLogger solver putCommentLine
      replicateM (length vsAssoc) (Simplex2.newVar solver) -- XXX
      Simplex2.setOptDir solver $ MIP.objDir $ MIP.objectiveFunction mip
      Simplex2.setObj solver $ fromJust (LAFOL.fromFOLExpr obj)
      putCommentLine "Loading constraints... "
      forM_ (cs1 ++ cs2) $ \c -> do
        Simplex2.assertAtom solver $ fromJust (LAFOL.fromFOLAtom c)
      putCommentLine "Loading constraints finished"

      mip <- MIPSolver2.newSolver solver ivs2
      MIPSolver2.setShowRational mip printRat
      MIPSolver2.setLogger mip putCommentLine
      MIPSolver2.setOnUpdateBestSolution mip $ \m val -> putOLine (showValue val)

      procs <-
        if nthreads >= 1
        then return nthreads
        else do
          ncap  <- getNumCapabilities
          procs <- getNumProcessors
          return $ max (procs - 1) ncap
      setNumCapabilities procs
      MIPSolver2.setNThread mip procs

      ret <- MIPSolver2.optimize mip
      case ret of
        Simplex2.Unsat -> do
          putSLine "UNSATISFIABLE"
          exitFailure
        Simplex2.Unbounded -> do
          putSLine "UNBOUNDED"
          Just m <- MIPSolver2.getBestModel mip
          let m2 = Map.fromAscList [(v, m IntMap.! (nameToVar Map.! v)) | v <- Set.toList vs]
          printModel m2
          exitFailure
        Simplex2.Optimum -> do
          Just m <- MIPSolver2.getBestModel mip
          putSLine "OPTIMUM FOUND"
          let m2 = Map.fromAscList [(v, m IntMap.! (nameToVar Map.! v)) | v <- Set.toList vs]
          printModel m2

    solveByCAD
      | not (IntSet.null ivs2) = do
          putSLine "UNKNOWN"
          putCommentLine "integer variables are not supported by CAD"
          exitFailure
      | otherwise = do
          let cs = map (fmap f) $ cs1 ++ cs2
              vs3 = Set.fromAscList $ IntSet.toAscList vs2
          case CAD.solve vs3 cs of
            Nothing -> do
              putSLine "UNSATISFIABLE"
              exitFailure
            Just m -> do
              let m2 = IntMap.map (\x -> AReal.approx x (2^^(-64::Int))) $
                         IntMap.fromAscList $ Map.toAscList $ m
              putOLine $ showValue (FOL.evalExpr m2 obj)
              putSLine "SATISFIABLE"
              let m3 = Map.fromAscList [(v, m2 IntMap.! (nameToVar Map.! v)) | v <- Set.toList vs]
              printModel m3
      where
        f (Const r)   = P.constant r
        f (Var v)     = P.var v
        f (e1 :+: e2) = f e1 + f e2
        f (e1 :*: e2) = f e1 * f e2
        f (e1 :/: e2)
          | P.deg p > 0 = error "can't handle rational expression"
          | otherwise   = P.mapCoeff (/ c) $ f e1 
          where
            p = f e2
            c = P.coeff P.mone p

    solveByContiTraverso
      | not (vs `Set.isSubsetOf` ivs) = do
          putSLine "UNKNOWN"
          putCommentLine "continuous variables are not supported by Conti-Traverso algorithm"
          exitFailure
      | otherwise = do
          let tmp = do
                linObj <- LAFOL.fromFOLExpr obj
                linCon <- mapM LAFOL.fromFOLAtom (cs1 ++ cs2)
                return (linObj, linCon)
          case tmp of
            Nothing -> do
              putSLine "UNKNOWN"
              putCommentLine "non-linear expressions are not supported by Conti-Traverso algorithm"
              exitFailure
            Just (linObj, linCon) -> do
              case ContiTraverso.solve P.grlex vs2 (MIP.objDir $ MIP.objectiveFunction mip) linObj linCon of
                Nothing -> do
                  putSLine "UNSATISFIABLE"
                  exitFailure
                Just m -> do
                  let m2 = IntMap.map fromInteger m
                  putOLine $ showValue (FOL.evalExpr m2 obj)
                  putSLine "OPTIMUM FOUND"
                  let m3 = Map.fromAscList [(v, m2 IntMap.! (nameToVar Map.! v)) | v <- Set.toList vs]
                  printModel m3

    printRat :: Bool
    printRat = PrintRational `elem` opt

    showValue :: Rational -> String
    showValue = showRational printRat

mipPrintModel :: Handle -> Bool -> Map MIP.Var Rational -> IO ()
mipPrintModel h asRat m = do
  forM_ (Map.toList m) $ \(v, val) -> do
    printf "v %s = %s\n" (MIP.fromVar v) (showRational asRat val)


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
                  ".lp"   -> ModeMIP
                  ".mps"  -> ModeMIP
                  _ -> ModeMIP

      case mode of
        ModeSAT -> do
          ret <- DIMACS.parseFile fname
          case ret of
            Left err -> hPrint stderr err >> exitFailure
            Right cnf -> do
              let (mip,mtrans) = SAT2IP.convert cnf
              run (getSolver o) o mip $ \m -> do
                let m2 = mtrans m
                satPrintModel stdout m2 0
                writeSOLFileSAT o m2
        ModePB -> do
          ret <- PBFileAttoparsec.parseOPBFile fname
          case ret of
            Left err -> hPutStrLn stderr err >> exitFailure
            Right pb -> do
              let (mip,mtrans) = PB2IP.convert pb
              run (getSolver o) o mip $ \m -> do
                let m2 = mtrans m
                pbPrintModel stdout m2 0
                writeSOLFileSAT o m2
        ModeWBO -> do
          ret <- PBFileAttoparsec.parseWBOFile fname
          case ret of
            Left err -> hPutStrLn stderr err >> exitFailure
            Right wbo -> do
              let (mip,mtrans) = PB2IP.convertWBO False wbo
              run (getSolver o) o mip $ \m -> do
                let m2 = mtrans m
                pbPrintModel stdout m2 0
                writeSOLFileSAT o m2
        ModeMaxSAT -> do
          ret <- MaxSAT.parseFile fname
          case ret of
            Left err -> hPutStrLn stderr err >> exitFailure
            Right wcnf -> do
              let (mip,mtrans) = MaxSAT2IP.convert False wcnf
              run (getSolver o) o mip $ \m -> do
                let m2 = mtrans m
                maxsatPrintModel stdout m2 0
                writeSOLFileSAT o m2
        ModeMIP -> do
          ret <- MIP.readFile fname
          mip <- case ret of
                  Right mip -> return mip
                  Left err -> hPrint stderr err >> exitFailure
          run (getSolver o) o mip $ \m -> do
            mipPrintModel stdout (PrintRational `elem` o) m
            writeSOLFileMIP o m
    (_,_,errs) ->
        hPutStrLn stderr $ concat errs ++ usageInfo header options

-- FIXME: 目的関数値を表示するように
writeSOLFileMIP :: [Flag] -> Map MIP.Var Rational -> IO ()
writeSOLFileMIP opt m = do
  let m2 = Map.fromList [(MIP.fromVar v, fromRational val) | (v,val) <- Map.toList m]
  writeSOLFileRaw opt m2

-- FIXME: 目的関数値を表示するように
writeSOLFileSAT :: [Flag] -> SAT.Model -> IO ()
writeSOLFileSAT opt m = do
  let m2 = Map.fromList [("x" ++ show x, if b then 1 else 0) | (x,b) <- assocs m]
  writeSOLFileRaw opt m2

writeSOLFileRaw :: [Flag] -> Map String Rational -> IO ()
writeSOLFileRaw opt m = do
  forM_ [fname | WriteFile fname <- opt ] $ \fname -> do
    let m2 = Map.map fromRational m
    writeFile fname (GurobiSol.render m2 Nothing)
