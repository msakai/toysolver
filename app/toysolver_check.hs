{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Control.Monad
import Data.Array.IArray
import Data.Char
import Data.Default.Class
import Data.IORef
import Data.List (intercalate, intersperse, sortBy)
import qualified Data.Map.Lazy as Map
import Data.Ord
import qualified Data.PseudoBoolean as PBFile
import Data.Scientific
import Data.String
import qualified Data.Text as T
import qualified Data.Version as V
import qualified Numeric.Optimization.MIP as MIP
import qualified Numeric.Optimization.MIP.Solution.Gurobi as GurobiSol
import Options.Applicative hiding (Const)
import System.Environment
import System.Exit
import System.FilePath
import System.IO
import Text.Printf

import qualified ToySolver.FileFormat as FF
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.SAT.Types as SAT
import ToySolver.Internal.Util (setEncodingChar8)
import ToySolver.Version


data Mode = ModeSAT | ModePB | ModeWBO | ModeMaxSAT | ModeMIP
  deriving (Eq, Ord, Show)

data Options = Options
  { optInputFile :: FilePath
  , optSolutionFile :: FilePath
  , optMode :: Maybe Mode
  , optFileEncoding :: Maybe String
  , optPBFastParser :: Bool
  , optMIPTol :: MIP.Tol Scientific
  }

optionsParser :: Parser Options
optionsParser = Options
  <$> fileInput
  <*> solutionFileInput
  <*> modeOption
  <*> fileEncodingOption
  <*> pbFastParserOption
  <*> mipTolOptions
  where
    fileInput :: Parser FilePath
    fileInput = argument str (metavar "FILE")

    solutionFileInput :: Parser FilePath
    solutionFileInput = argument str (metavar "SOLUTION_FILE")

    modeOption :: Parser (Maybe Mode)
    modeOption = optional $
          flag' ModeSAT    (long "sat"    <> help "load boolean satisfiability problem in .cnf file")
      <|> flag' ModePB     (long "pb"     <> help "load pseudo boolean problem in .opb file")
      <|> flag' ModeWBO    (long "wbo"    <> help "load weighted boolean optimization problem in .wbo file")
      <|> flag' ModeMaxSAT (long "maxsat" <> help "load MaxSAT problem in .cnf or .wcnf file")
      <|> flag' ModeMIP    (long "lp"     <> help "load LP/MIP problem in .lp or .mps file")

    fileEncodingOption :: Parser (Maybe String)
    fileEncodingOption = optional $ strOption
      $  long "encoding"
      <> metavar "ENCODING"
      <> help "file encoding for LP/MPS files"

    pbFastParserOption :: Parser Bool
    pbFastParserOption = switch
      $  long "pb-fast-parser"
      <> help "use attoparsec-based parser instead of megaparsec-based one for speed"

    mipTolOptions :: Parser (MIP.Tol Scientific)
    mipTolOptions = MIP.Tol <$> intTol <*> feasTol <*> optTol
      where
        intTol = option auto
          $  long "tol-integrality"
          <> metavar "REAL"
          <> help "If a value of integer variable is within this amount from its nearest integer, it is considered feasible."
          <> value (MIP.integralityTol def)
          <> showDefault
        feasTol = option auto
          $  long "tol-feasibility"
          <> metavar "REAL"
          <> help "If the amount of violation of constraints is within this amount, it is considered feasible."
          <> value (MIP.feasibilityTol def)
          <> showDefault
        optTol = option auto
          $  long "tol-optimality"
          <> metavar "REAL"
          <> help "Feasiblity tolerance of dual constraints."
          <> value (MIP.optimalityTol def)
          <> showDefault

parserInfo :: ParserInfo Options
parserInfo = info (helper <*> versionOption <*> optionsParser)
  $  fullDesc
  <> header "toysolver-check - a solution checker"
  where
    versionOption :: Parser (a -> a)
    versionOption = infoOption (V.showVersion version)
      $  hidden
      <> long "version"
      <> help "Show version"

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif

  errorRef <- newIORef False

  opt <- execParser parserInfo
  let mode =
        case optMode opt of
          Just m  -> m
          Nothing ->
            case getExt (optInputFile opt) of
              ".cnf"  -> ModeSAT
              ".opb"  -> ModePB
              ".wbo"  -> ModeWBO
              ".wcnf" -> ModeMaxSAT
              ".lp"   -> ModeMIP
              ".mps"  -> ModeMIP
              _ -> ModeSAT

  case mode of
    ModeSAT -> do
      cnf  <- FF.readFile (optInputFile opt)
      model <- liftM parseSATLog (readFile (optSolutionFile opt))

      forM_ (CNF.cnfClauses cnf) $ \constr ->
        unless (SAT.evalClause model (SAT.unpackClause constr)) $ do
          printf "violated: %s\n" (showClause constr :: String)
          writeIORef errorRef True

    ModePB -> do
      opb <-
        if optPBFastParser opt then
          liftM FF.unWithFastParser $ FF.readFile (optInputFile opt)
        else
          FF.readFile (optInputFile opt)
      model <- liftM parsePBLog (readFile (optSolutionFile opt))

      case PBFile.pbObjectiveFunction opb of
        Nothing -> return ()
        Just obj -> putStrLn $ "objective value = " ++ show (SAT.evalPBSum model obj)
      forM_ (PBFile.pbConstraints opb) $ \constr -> do
        unless (SAT.evalPBConstraint model constr) $ do
          printf "violated: %s\n" (showPBConstraint constr :: String)
          writeIORef errorRef True

    ModeWBO -> do
      wbo <-
        if optPBFastParser opt then
          liftM FF.unWithFastParser $ FF.readFile (optInputFile opt)
        else
          FF.readFile (optInputFile opt)
      model <- liftM parsePBLog (readFile (optSolutionFile opt))

      cost <- fmap sum $ forM (PBFile.wboConstraints wbo) $ \(w, constr) -> do
        if SAT.evalPBConstraint model constr then
          return 0
        else do
          case w of
            Nothing -> do
              printf "violated hard constraint: %s\n" (showPBConstraint constr :: String)
              writeIORef errorRef True
              return 0
            Just w' -> do
              return w'
      putStrLn $ "total cost = " ++ show cost

      case PBFile.wboTopCost wbo of
        Just top | top <= cost -> do
          printf "total cost is greater than or equal to top cost (%d)\n" top
          writeIORef errorRef True
        _ -> return ()

    ModeMaxSAT -> do
      wcnf  <- FF.readFile (optInputFile opt)
      model <- liftM parseMaxSATLog (readFile (optSolutionFile opt))

      cost <- fmap sum $ forM (CNF.wcnfClauses wcnf) $ \(w, constr) ->
        if SAT.evalClause model (SAT.unpackClause constr) then do
          return 0
        else if w == CNF.wcnfTopCost wcnf then do
          printf "violated hard constraint: %s\n" (showClause constr :: String)
          return 0
        else do
          return w
      putStrLn $ "total cost = " ++ show cost

    ModeMIP -> do
      enc <- mapM mkTextEncoding $ optFileEncoding opt
      mip <- MIP.readFile def{ MIP.optFileEncoding = enc } (optInputFile opt)

      sol <- GurobiSol.readFile (optSolutionFile opt)
      let m = MIP.solVariables sol
          tol = optMIPTol opt

      let objVal = MIP.eval tol m (MIP.objExpr (MIP.objectiveFunction mip))
      putStrLn $ "objective value = " ++ show objVal
      case MIP.solObjectiveValue sol of
        Nothing -> return ()
        Just declaredObjVal -> do
          unless (abs (objVal - declaredObjVal) <= MIP.feasibilityTol tol) $ do
            printf "declared objective value (%s) does not match to the computed value (%s)\n"
              (show declaredObjVal) (show objVal)

      forM (Map.toList (MIP.varDomains mip)) $ \(v, (vt, bounds@(lb,ub))) -> do
        let val = MIP.eval tol m v
            flag1 =
              case vt of
                MIP.ContinuousVariable -> True
                MIP.SemiContinuousVariable -> True
                MIP.IntegerVariable -> isIntegral tol val
                MIP.SemiIntegerVariable -> isIntegral tol val
            flag2 =
              case vt of
                MIP.ContinuousVariable -> isInBounds tol bounds val
                MIP.IntegerVariable -> isInBounds tol bounds val
                MIP.SemiIntegerVariable -> isInBounds tol (0,0) val || isInBounds tol bounds val
                MIP.SemiContinuousVariable -> isInBounds tol (0,0) val || isInBounds tol bounds val
        unless flag1 $ do
          writeIORef errorRef True
          printf "variable %s is not integral\n" (T.unpack (MIP.varName v))
        unless flag2 $ do
          writeIORef errorRef True
          let f MIP.NegInf = "-inf"
              f MIP.PosInf = "+inf"
              f (MIP.Finite x) = show x
          printf "variable %s is out of bounds lb=%s ub=%s\n" (T.unpack (MIP.varName v)) (f lb) (f ub)

      forM_ (MIP.constraints mip) $ \constr -> do
        unless (MIP.eval tol m constr) $ do
          writeIORef errorRef True
          case MIP.constrLabel constr of
            Just name -> printf "violated: %s\n" (T.unpack name)
            Nothing -> printf "violated: %s\n" (showMIPConstraint constr)

      forM_ (MIP.sosConstraints mip) $ \constr -> do
        unless (MIP.eval tol m constr) $ do
          writeIORef errorRef True
          case MIP.sosLabel constr of
            Just name -> printf "violated: %s\n" (T.unpack name)
            Nothing -> printf "violated: %s\n" (showMIPSOSConstraint constr)

      return ()

  errored <- readIORef errorRef
  when errored $ exitFailure

getExt :: String -> String
getExt name | (base, ext) <- splitExtension name =
  case map toLower ext of
#ifdef WITH_ZLIB
    ".gz" -> getExt base
#endif
    s -> s

showClause :: (Monoid a, IsString a) => SAT.PackedClause -> a
showClause = foldr (\f g -> f <> fromString " " <> g) mempty . map (fromString . show) . SAT.unpackClause

showPBSum :: (Monoid a, IsString a) => PBFile.Sum -> a
showPBSum = mconcat . map showWeightedTerm
  where
    showWeightedTerm :: (Monoid a, IsString a) => PBFile.WeightedTerm -> a
    showWeightedTerm (c, lits) = foldr (\f g -> f <> fromString " " <> g) mempty (x:xs)
      where
        x = if c >= 0 then fromString "+" <> fromString (show c) else fromString (show c)
        xs = map showLit $ sortBy (comparing abs) lits

    showLit :: (Monoid a, IsString a) => PBFile.Lit -> a
    showLit lit = if lit > 0 then v else fromString "~" <> v
      where
        v = fromString "x" <> fromString (show (abs lit))

showPBConstraint :: (Monoid a, IsString a) => PBFile.Constraint -> a
showPBConstraint (lhs, op, rhs) =
  showPBSum lhs <> f op <>  fromString " " <> fromString (show rhs) <> fromString ";\n"
  where
    f PBFile.Eq = fromString "="
    f PBFile.Ge = fromString ">="

showMIPConstraint :: MIP.Constraint Scientific -> String
showMIPConstraint constr = concat
  [ case MIP.constrIndicator constr of
      Nothing -> ""
      Just (MIP.Var var, val) ->
        let rhs =
              case floatingOrInteger val of
                Right (i :: Integer) -> show i
                Left (_ :: Double) -> show val  -- should be error?
         in T.unpack var ++ " = " ++ rhs ++ " -> "
  , case MIP.constrLB constr of
      MIP.NegInf -> ""
      MIP.PosInf -> "+inf <= "
      MIP.Finite x -> show x ++ " <= "
  , showMIPExpr (MIP.constrExpr constr)
  , case MIP.constrUB constr of
      MIP.NegInf -> "<= -inf"
      MIP.PosInf -> ""
      MIP.Finite x -> " <= " ++ show x
  ]

showMIPSOSConstraint :: MIP.SOSConstraint Scientific -> String
showMIPSOSConstraint constr = concat $
  [show (MIP.sosType constr), " ::"] ++ [
    " " ++ T.unpack (MIP.varName v) ++ " : " ++ show r
  | (v, r) <- MIP.sosBody constr
  ]

showMIPExpr :: MIP.Expr Scientific -> String
showMIPExpr e = intercalate " "
  [ intercalate "*" (((if c >= 0 then "+" ++ show c else show c) : map (T.unpack . MIP.varName) vs))
  | MIP.Term c vs <- MIP.terms e
  ]

parsePBLog :: String -> SAT.Model
parsePBLog s = array (1, maximum (0 : map fst ls2)) ls2
  where
    ls = lines s
    ls2 = do
      l <- ls
      case l of
        'v':xs -> do
          w <- words xs
          case w of
            '-':'x':ys -> return (read ys, False)
            'x':ys -> return (read ys, True)
        _ -> mzero

parseMaxSATLog :: String -> SAT.Model
parseMaxSATLog s =
  case f (lines s) Nothing [] of
    (obj, vlines) ->
      let tmp = [c | c <- concat vlines, not (isSpace c)]
       in if all (\c -> c == '0' || c == '1') tmp then
            array (1, length tmp) [(v, c=='1') | (v, c) <- zip [1..] tmp]
          else
            let ys = [if l > 0 then (l, True) else (-l, False) | vline <- vlines, w <- words vline, let l = read w]
             in array (1, maximum (0 : map fst ys)) ys
  where
    f :: [String] -> Maybe Integer -> [String] -> (Maybe Integer, [String])
    f [] obj vlines = (obj, reverse vlines)
    f (l : ls) obj vlines =
      case l of
        'o':xs -> f ls (Just (read (dropWhile isSpace xs))) []
        'v':xs -> f ls obj (dropWhile isSpace xs : vlines)
        _ -> f ls obj vlines

parseSATLog :: String -> SAT.Model
parseSATLog s = array (1, maximum (0 : map fst ys)) ys
  where
    xs = do
      l <- lines s
      case l of
        'v':xs -> map read (words xs)
        _ -> mzero
    ys = [if y > 0 then (y, True) else (-y, False) | y <- takeWhile (0 /=) xs]

isIntegral :: RealFrac r => MIP.Tol r -> r -> Bool
isIntegral tol x = abs (x - fromIntegral (floor (x + 0.5) :: Integer)) <= MIP.integralityTol tol

isInBounds :: (Num r, Ord r) => MIP.Tol r -> MIP.Bounds r -> r -> Bool
isInBounds tol (lb, ub) x =
  lb - MIP.Finite (MIP.feasibilityTol tol) <= MIP.Finite x &&
  MIP.Finite x <= ub + MIP.Finite (MIP.feasibilityTol tol)
