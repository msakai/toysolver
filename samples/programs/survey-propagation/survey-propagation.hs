{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
import Control.Exception
import Control.Monad
import Data.Default.Class
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
import qualified ToySolver.FileFormat as FF
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.SAT.Solver.MessagePassing.SurveyPropagation as SP

data Options
  = Options
  { optNThreads :: Int
  }

instance Default Options where
  def =
    Options
    { optNThreads = 1
    }

options :: [OptDescr (Options -> Options)]
options =
  [ Option [] ["threads"] (ReqArg (\val opt -> opt{ optNThreads = read val }) "<integer>") "number of threads"
  ]

showHelp :: Handle -> IO ()
showHelp h = hPutStrLn h (usageInfo header options)

header :: String
header = unlines
  [ "Usage:"
  , "  spcl [OPTION]... [file.cnf|file.wcnf]"
  , ""
  , "Options:"
  ]

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (_,_,errs@(_:_)) -> do
      mapM_ putStrLn errs
      exitFailure

    (o,[fname],_) -> do
      let opt = foldl (flip id) def o
      handle (\(e::SomeException) -> hPrint stderr e) $ do
        wcnf <- FF.readFile fname
        solver <- SP.newSolver
          (CNF.wcnfNumVars wcnf) [(fromIntegral w, clause) | (w,clause) <- CNF.wcnfClauses wcnf]
        SP.setNThreads solver (optNThreads opt)
        -- Rand.withSystemRandom $ SP.initializeRandom solver
        print =<< SP.propagate solver
        forM_ [1 .. CNF.wcnfNumVars wcnf] $ \v -> do
          prob <- SP.getVarProb solver v
          print (v,prob)
        SP.deleteSolver solver

    _ -> do
       showHelp stderr
