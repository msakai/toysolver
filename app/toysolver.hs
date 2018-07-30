{-# LANGUAGE CPP #-}
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
import Data.Monoid
import Data.Ratio
import Data.Scientific (Scientific)
import qualified Data.Scientific as Scientific
import Data.String
import qualified Data.Version as V
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Traversable as T
import Options.Applicative hiding (Const)
import System.Exit
import System.Environment
import System.FilePath
import System.Console.GetOpt
import System.IO
import Text.Printf
import GHC.Conc (getNumProcessors, setNumCapabilities)

import Data.OptDir
import qualified Data.PseudoBoolean as PBFile
import qualified Data.PseudoBoolean.Attoparsec as PBFileAttoparsec

import ToySolver.Data.OrdRel
import ToySolver.Data.FOL.Arith as FOL
import qualified ToySolver.Data.LA as LA
import qualified ToySolver.Data.LA.FOL as LAFOL
import qualified ToySolver.Data.Polynomial as P
import qualified ToySolver.Data.AlgebraicNumber.Real as AReal
import qualified ToySolver.Data.MIP as MIP
import qualified ToySolver.Data.MIP.Solution.Gurobi as GurobiSol
import qualified ToySolver.Arith.OmegaTest as OmegaTest
import qualified ToySolver.Arith.Cooper as Cooper
import qualified ToySolver.Arith.Simplex.Textbook.MIPSolver.Simple as TextbookMIP
import qualified ToySolver.Arith.Simplex as Simplex
import qualified ToySolver.Arith.MIP as MIPSolver
import qualified ToySolver.Arith.CAD as CAD
import qualified ToySolver.Arith.ContiTraverso as ContiTraverso
import qualified ToySolver.FileFormat as FF
import ToySolver.Converter
import ToySolver.SAT.Printer
import qualified ToySolver.SAT.Types as SAT
import ToySolver.Version
import ToySolver.Internal.Util

-- ---------------------------------------------------------------------------

data Mode = ModeSAT | ModePB | ModeWBO | ModeMaxSAT | ModeMIP
  deriving (Eq, Ord, Show)

data Options = Options
  { optInput :: FilePath
  , optMode :: Maybe Mode
  , optSolver :: String
  , optPrintRational :: Bool
  , optWriteFile :: Maybe FilePath
  , optNoMIP :: Bool
  , optPivotStrategy :: Simplex.PivotStrategy -- String
  , optBoundTightening :: Bool
  , optNThread :: Int
  , optOmegaReal :: String
  , optFileEncoding :: Maybe String
  } deriving (Eq, Show)

optionsParser :: Parser Options
optionsParser = Options
  <$> fileInput
  <*> modeOption
  <*> solverOption
  <*> printRationalOption
  <*> writeFileOption
  <*> noMIPOption
  <*> pivotStrategyOption
  <*> boundTighteningOption
  <*> nThreadOption
  <*> omegaRealOption
  <*> fileEncodingOption
  where
    fileInput :: Parser FilePath
    fileInput = argument str (metavar "FILE")

    modeOption :: Parser (Maybe Mode)
    modeOption = optional $
          flag' ModeSAT    (long "sat"    <> help "solve boolean satisfiability problem in .cnf file")
      <|> flag' ModePB     (long "pb"     <> help "solve pseudo boolean problem in .opb file")
      <|> flag' ModeWBO    (long "wbo"    <> help "solve weighted boolean optimization problem in .wbo file")
      <|> flag' ModeMaxSAT (long "maxsat" <> help "solve MaxSAT problem in .cnf or .wcnf file")
      <|> flag' ModeMIP    (long "lp"     <> help "solve LP/MIP problem in .lp or .mps file")

    solverOption :: Parser String
    solverOption = strOption
      $  long "solver"
      <> metavar "SOLVER"
      <> help "Solver algorithm: mip, omega-test, cooper, cad, old-mip, ct"
      <> value "mip"
      <> showDefaultWith id

    printRationalOption :: Parser Bool
    printRationalOption = switch
      $  long "print-rational"
      <> help "print rational numbers instead of decimals"

    writeFileOption :: Parser (Maybe FilePath)
    writeFileOption = optional $ strOption
      $  short 'w'
      <> metavar "FILE"
      <> help "write solution to filename in Gurobi .sol format"

    noMIPOption :: Parser Bool
    noMIPOption = switch
      $  long "nomip"
      <> help "consider all integer variables as continuous"

    pivotStrategyOption :: Parser Simplex.PivotStrategy
    pivotStrategyOption = option (maybeReader Simplex.parsePivotStrategy)
      $  long "pivot-strategy"
      <> metavar "NAME"
      <> help ("pivot strategy for simplex: " ++ intercalate ", " [Simplex.showPivotStrategy ps | ps <- [minBound..maxBound]])
      <> value (Simplex.configPivotStrategy def)
      <> showDefaultWith Simplex.showPivotStrategy

    boundTighteningOption :: Parser Bool
    boundTighteningOption =  switch
      $  long "bound-tightening"
      <> help "enable bound tightening in simplex algorithm"

    nThreadOption :: Parser Int
    nThreadOption = option auto
      $  long "threads"
      <> metavar "INT"
      <> help "number of threads to use (0: auto)"
      <> value 0
      <> showDefault

    omegaRealOption :: Parser String
    omegaRealOption = strOption
      $  long "omega-real"
      <> metavar "SOLVER"
      <> help "fourier-motzkin, virtual-substitution (or vs), cad, simplex, none"
      <> value "fourier-motzkin"
      <> showDefaultWith id

    fileEncodingOption :: Parser (Maybe String)
    fileEncodingOption = optional $ strOption
      $  long "encoding"
      <> metavar "ENCODING"
      <> help "file encoding for LP/MPS files"

parserInfo :: ParserInfo Options
parserInfo = info (helper <*> versionOption <*> optionsParser)
  $  fullDesc
  <> header "toysolver - a solver for arithmetic problems"
  where
    versionOption :: Parser (a -> a)
    versionOption = infoOption (V.showVersion version)
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

-- ---------------------------------------------------------------------------

run
  :: String
  -> Options
  -> MIP.Problem Rational
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

    compileE :: MIP.Expr Rational -> Expr Rational
    compileE = foldr (+) (Const 0) . map compileT . MIP.terms

    compileT :: MIP.Term Rational -> Expr Rational
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
                MIP.PosInf -> [OrdRel 1 Le 0] -- False
                MIP.Finite x -> [OrdRel e2 Ge (Const x)]
            , case ub of
                MIP.NegInf -> [OrdRel 1 Le 0] -- False
                MIP.PosInf -> []
                MIP.Finite x -> [OrdRel e2 Le (Const x)]
            ]
        Just _ -> error "indicator constraint is not supported yet"

    ivs
      | optNoMIP opt = Set.empty
      | otherwise    = MIP.integerVariables mip

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
               case optOmegaReal opt of
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
          case TextbookMIP.optimize (MIP.objDir $ MIP.objectiveFunction mip) obj' cs' ivs2 of
            TextbookMIP.OptUnsat -> do
              putSLine "UNSATISFIABLE"
              exitFailure
            TextbookMIP.Unbounded -> do
              putSLine "UNBOUNDED"
              exitFailure
            TextbookMIP.Optimum r m -> do
              putOLine $ showValue r
              putSLine "OPTIMUM FOUND"
              let m2 = Map.fromAscList [(v, m IntMap.! (nameToVar Map.! v)) | v <- Set.toList vs]
              printModel m2

    solveByMIP2 = do
      solver <- Simplex.newSolver

      let config =
            def
            { Simplex.configPivotStrategy = optPivotStrategy opt
            , Simplex.configEnableBoundTightening = optBoundTightening opt
            }
          nthreads = optNThread opt

      Simplex.setConfig solver config
      Simplex.setLogger solver putCommentLine
      Simplex.enableTimeRecording solver
      replicateM (length vsAssoc) (Simplex.newVar solver) -- XXX
      Simplex.setOptDir solver $ MIP.objDir $ MIP.objectiveFunction mip
      Simplex.setObj solver $ fromJust (LAFOL.fromFOLExpr obj)
      putCommentLine "Loading constraints... "
      forM_ (cs1 ++ cs2) $ \c -> do
        Simplex.assertAtom solver $ fromJust (LAFOL.fromFOLAtom c)
      putCommentLine "Loading constraints finished"

      mip <- MIPSolver.newSolver solver ivs2
      MIPSolver.setShowRational mip printRat
      MIPSolver.setLogger mip putCommentLine
      MIPSolver.setOnUpdateBestSolution mip $ \m val -> putOLine (showValue val)

      procs <-
        if nthreads >= 1
        then return nthreads
        else do
          ncap  <- getNumCapabilities
          procs <- getNumProcessors
          return $ max (procs - 1) ncap
      setNumCapabilities procs
      MIPSolver.setNThread mip procs

      ret <- MIPSolver.optimize mip
      case ret of
        Simplex.Unsat -> do
          putSLine "UNSATISFIABLE"
          exitFailure
        Simplex.Unbounded -> do
          putSLine "UNBOUNDED"
          Just m <- MIPSolver.getBestModel mip
          let m2 = Map.fromAscList [(v, m IntMap.! (nameToVar Map.! v)) | v <- Set.toList vs]
          printModel m2
          exitFailure
        Simplex.Optimum -> do
          Just m <- MIPSolver.getBestModel mip
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
    printRat = optPrintRational opt

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

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif

  o <- execParser parserInfo

  case fromMaybe ModeMIP (optMode o) of
    ModeSAT -> do
      cnf <- FF.readFile (optInput o)
      let (mip,info) = sat2ip cnf
      run (optSolver o) o (fmap fromInteger mip) $ \m -> do
        let m2 = transformBackward info m
        satPrintModel stdout m2 0
        writeSOLFileSAT o m2
    ModePB -> do
      ret <- PBFileAttoparsec.parseOPBFile (optInput o)
      case ret of
        Left err -> hPutStrLn stderr err >> exitFailure
        Right pb -> do
          let (mip,info) = pb2ip pb
          run (optSolver o) o (fmap fromInteger mip) $ \m -> do
            let m2 = transformBackward info m
            pbPrintModel stdout m2 0
            writeSOLFileSAT o m2
    ModeWBO -> do
      ret <- PBFileAttoparsec.parseWBOFile (optInput o)
      case ret of
        Left err -> hPutStrLn stderr err >> exitFailure
        Right wbo -> do
          let (mip,info) = wbo2ip False wbo
          run (optSolver o) o (fmap fromInteger mip) $ \m -> do
            let m2 = transformBackward info m
            pbPrintModel stdout m2 0
            writeSOLFileSAT o m2
    ModeMaxSAT -> do
      wcnf <- FF.readFile (optInput o)
      let (mip,info) = maxsat2ip False wcnf
      run (optSolver o) o (fmap fromInteger mip) $ \m -> do
        let m2 = transformBackward info m
        maxsatPrintModel stdout m2 0
        writeSOLFileSAT o m2
    ModeMIP -> do
      enc <- T.mapM mkTextEncoding $ optFileEncoding o
      mip <- MIP.readFile def{ MIP.optFileEncoding = enc } (optInput o)
      run (optSolver o) o (fmap toRational mip) $ \m -> do
        mipPrintModel stdout (optPrintRational o) m
        writeSOLFileMIP o m

-- FIXME: 目的関数値を表示するように
writeSOLFileMIP :: Options -> Map MIP.Var Rational -> IO ()
writeSOLFileMIP opt m = do
  let sol = MIP.Solution
            { MIP.solStatus = MIP.StatusUnknown
            , MIP.solObjectiveValue = Nothing
            , MIP.solVariables = Map.fromList [(v, Scientific.fromFloatDigits (fromRational val :: Double)) | (v,val) <- Map.toList m]
            }
  writeSOLFileRaw opt sol

-- FIXME: 目的関数値を表示するように
writeSOLFileSAT :: Options -> SAT.Model -> IO ()
writeSOLFileSAT opt m = do
  let sol = MIP.Solution
            { MIP.solStatus = MIP.StatusUnknown
            , MIP.solObjectiveValue = Nothing
            , MIP.solVariables = Map.fromList [(fromString ("x" ++ show x), if b then 1 else 0) | (x,b) <- assocs m]
            }
  writeSOLFileRaw opt sol

writeSOLFileRaw :: Options -> MIP.Solution Scientific -> IO ()
writeSOLFileRaw opt sol = do
  case optWriteFile opt of
    Just fname -> GurobiSol.writeFile fname sol
    Nothing -> return ()

