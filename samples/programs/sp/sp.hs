{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
import Control.Exception
import Control.Monad
import Data.Default.Class
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
import qualified ToySolver.Text.MaxSAT as MaxSAT
import qualified ToySolver.SAT.MessagePassing.SurveyPropagation as SP
#ifdef ENABLE_OPENCL
import Control.Parallel.OpenCL
import qualified ToySolver.SAT.MessagePassing.SurveyPropagation.OpenCL as SPCL
#endif

data Options
  = Options
  { optOpenCL :: Bool
  , optNThreads :: Int
  }

instance Default Options where
  def =
    Options
    { optOpenCL = False
    , optNThreads = 1
    }

options :: [OptDescr (Options -> Options)]
options =
  [ Option [] ["opencl"] (NoArg (\opt -> opt{ optOpenCL = True })) "use OpenCL version"
  , Option [] ["threads"] (ReqArg (\val opt -> opt{ optNThreads = read val }) "<integer>") "number of threads"
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
        Right wcnf <- MaxSAT.parseFile fname

#ifdef ENABLE_OPENCL
        if optOpenCL opt then do
          ids@(platform:_) <- clGetPlatformIDs
          (dev:_) <- clGetDeviceIDs platform CL_DEVICE_TYPE_ALL
          context <- clCreateContext [] [dev] print
          solver <- SPCL.newSolver putStrLn context dev
            (MaxSAT.numVars wcnf) [(fromIntegral w, clause) | (w,clause) <- MaxSAT.clauses wcnf]
          -- Rand.withSystemRandom $ SPCL.initializeRandom solver
          print =<< SPCL.propagate solver
          forM_ [1 .. MaxSAT.numVars wcnf] $ \v -> do
            prob <- SPCL.getVarProb solver v
            print (v,prob)
          SPCL.deleteSolver solver
#else
        if False then do
          return ()
#endif
        else do
          solver <- SP.newSolver
            (MaxSAT.numVars wcnf) [(fromIntegral w, clause) | (w,clause) <- MaxSAT.clauses wcnf]
          SP.setNThreads solver (optNThreads opt)
          -- Rand.withSystemRandom $ SP.initializeRandom solver
          print =<< SP.propagate solver
          forM_ [1 .. MaxSAT.numVars wcnf] $ \v -> do
            prob <- SP.getVarProb solver v
            print (v,prob)
          SP.deleteSolver solver

    _ -> do
       showHelp stderr
