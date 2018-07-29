module Main where

import Control.Monad
import Data.Char
import Data.Default.Class
import Data.Monoid
import qualified Data.Vector.Unboxed as VU
import Options.Applicative
import System.Clock
import System.IO
import qualified System.Random.MWC as Rand
import Text.Printf

import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.SAT.SLS.ProbSAT as ProbSAT
import ToySolver.SAT.Printer (maxsatPrintModel)

data Options = Options
  { optAlgorithm :: String
  , optFileName :: FilePath
  , optOptions :: ProbSAT.Options
  , optRandomSeed :: Maybe Rand.Seed
  , optProbSATFunc :: String
  , optProbSATCB :: Double
  , optProbSATCM :: Double
  , optWalkSATP :: Double
  } deriving (Eq, Show)

optionsParser :: Parser Options
optionsParser = Options
  <$> algOption
  <*> fileInput
  <*> solverOptions
  <*> randomSeedOption
  <*> func
  <*> cb
  <*> cm
  <*> p
  where
    fileInput :: Parser FilePath
    fileInput = argument str (metavar "FILE")

    algOption :: Parser String
    algOption = strOption
      $  long "alg"
      <> metavar "ALGORITHM"
      <> help "Algorithm: walksat, probsat"
      <> value "probsat"
      <> showDefaultWith id

    solverOptions :: Parser ProbSAT.Options
    solverOptions = ProbSAT.Options
      <$> targetOption
      <*> maxTriesOption
      <*> maxFlipsOption
      <*> pickClauseWeightedOption

    randomSeedOption :: Parser (Maybe Rand.Seed)
    randomSeedOption = optional $
      (fmap (Rand.toSeed . VU.fromList . map read . words)) $
      strOption $
        mconcat
        [ long "random-seed"
        , metavar "\"INT ..\""
        , help "random seed"
        ]

    targetOption :: Parser Integer
    targetOption = option auto
      $  long "target"
      <> help "target objective value"
      <> showDefault
      <> metavar "INT"
      <> value (ProbSAT.optTarget def)

    maxTriesOption :: Parser Int
    maxTriesOption = option auto
      $  long "max-tries"
      <> help "maximum number of tries"
      <> showDefault
      <> metavar "INT"
      <> value (ProbSAT.optMaxTries def)

    maxFlipsOption :: Parser Int
    maxFlipsOption = option auto
      $  long "max-flips"
      <> help "maximum number of flips per try"
      <> showDefault
      <> metavar "INT"
      <> value (ProbSAT.optMaxFlips def)

    pickClauseWeightedOption :: Parser Bool
    pickClauseWeightedOption = switch
      $  short 'w'
      <> long "weighted"
      <> help "enable weighted clause selection"
      <> showDefault

    func :: Parser String
    func = strOption
      $  long "probsat-func"
      <> help "function type: exp, poly"
      <> showDefaultWith id
      <> metavar "FUNC"
      <> value "exp"

    cb :: Parser Double
    cb = option auto
      $  long "probsat-cb"
      <> help "c_b parameter"
      <> showDefault
      <> metavar "REAL"
      <> value 3.6

    cm :: Parser Double
    cm = option auto
      $  long "probsat-cm"
      <> help "c_m parameter"
      <> showDefault
      <> metavar "REAL"
      <> value 0.5

    p :: Parser Double
    p = option auto
      $  long "walksat-p"
      <> help "p parameter"
      <> showDefault
      <> metavar "REAL"
      <> value 0.1

parserInfo :: ParserInfo Options
parserInfo = info (helper <*> optionsParser)
  $  fullDesc
  <> header "probsat - an example program of ToySolver.SAT.SLS.ProbSAT"

main :: IO ()
main = do
  opt <- execParser parserInfo
  wcnf <- CNF.readFile (optFileName opt)
  solver <- ProbSAT.newSolverWeighted wcnf
  gen <-
    case optRandomSeed opt of
      Nothing -> Rand.createSystemRandom
      Just seed -> Rand.restore seed
  seed <- Rand.save gen
  putStrLn $ "c use --random-seed=" ++ show (unwords . map show . VU.toList . Rand.fromSeed $ seed) ++ " option to reproduce the execution"
  ProbSAT.setRandomGen solver gen
  let callbacks =
        def
        { ProbSAT.cbOnUpdateBestSolution = \_solver obj _sol -> printf "o %d\n" obj
        }
  case map toLower (optAlgorithm opt) of
    "walksat" -> do
      let p = optWalkSATP opt
      ProbSAT.walksat solver (optOptions opt) callbacks p
    "probsat" -> do
      let cb = optProbSATCB opt
          cm = optProbSATCM opt
      seq cb $ seq cm $ return ()
      case map toLower (optProbSATFunc opt) of
        "exp" -> do
          let f make break = cm**make / cb**break
          ProbSAT.probsat solver (optOptions opt) callbacks f
        "poly" -> do
          let eps = 1
              f make break = make**cm / (eps + break**cb)
          ProbSAT.probsat solver (optOptions opt) callbacks f
        _ -> error ("unknown function type: " ++ optProbSATFunc opt)
    _ -> error ("unknown algorithm name: " ++ optAlgorithm opt)
  (obj,sol) <- ProbSAT.getBestSolution solver
  stat <- ProbSAT.getStatistics solver
  printf "c TotalCPUTime = %fs\n" (fromIntegral (toNanoSecs (ProbSAT.statTotalCPUTime stat)) / 10^(9::Int) :: Double)
  printf "c FlipsPerSecond = %f\n" (ProbSAT.statFlipsPerSecond stat)
  when (obj == 0) $ do
    putStrLn "s OPTIMUM FOUND"
  maxsatPrintModel stdout sol (CNF.wcnfNumVars wcnf)
