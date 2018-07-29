{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
import Control.Exception
import Control.Monad
import Data.Default.Class
import Data.List
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.SAT.MessagePassing.SurveyPropagation as SP
#ifdef ENABLE_OPENCL
import Control.Parallel.OpenCL
import qualified ToySolver.SAT.MessagePassing.SurveyPropagation.OpenCL as SPCL
#endif

data Options
  = Options
  { optOpenCL :: Bool
  , optOpenCLPlatform :: Maybe String
  , optOpenCLDevice :: Int
  , optNThreads :: Int
  }

instance Default Options where
  def =
    Options
    { optOpenCL = False
    , optOpenCLPlatform = Nothing
    , optOpenCLDevice = 0
    , optNThreads = 1
    }

options :: [OptDescr (Options -> Options)]
options =
  [ Option [] ["opencl"] (NoArg (\opt -> opt{ optOpenCL = True })) "use OpenCL version"
  , Option [] ["opencl-platform"] (ReqArg (\val opt -> opt{ optOpenCLPlatform = Just val }) "<string>") "OpenCL platform to use"
  , Option [] ["opencl-device"] (ReqArg (\val opt -> opt{ optOpenCLDevice = read val }) "<integer>") "OpenCL device to use"
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

#ifdef ENABLE_OPENCL

getPlatform :: Maybe String -> IO CLPlatformID
getPlatform m = do
  putStrLn "Listing OpenCL platforms..."
  platforms <- clGetPlatformIDs
  case platforms of
    [] -> error "No OpenCL platform found"
    _ -> do
      tbl <- forM platforms $ \platform -> do
        s <- clGetPlatformInfo platform CL_PLATFORM_NAME
        devs <- clGetDeviceIDs platform CL_DEVICE_TYPE_ALL
        putStrLn $ "  " ++ s ++ " (" ++ show (length devs) ++ " devices)"
        forM_ (zip [0..] devs) $ \(i,dev) -> do
          devname <- clGetDeviceName dev 
          ts <- clGetDeviceType dev
          let f t =
                case t of
                  CL_DEVICE_TYPE_CPU -> "CPU"
                  CL_DEVICE_TYPE_GPU -> "GPU"
                  CL_DEVICE_TYPE_ACCELERATOR -> "ACCELERATOR"
                  CL_DEVICE_TYPE_DEFAULT -> "DEFAULT"
                  CL_DEVICE_TYPE_ALL -> "ALL"
          putStrLn $ "    " ++ show i ++ ": " ++ devname ++ " (" ++ intercalate "," (map f ts) ++ ")"
        return (s,platform)
      case m of
        Nothing -> return (snd (head tbl))
        Just name ->
          case lookup name tbl of
            Nothing -> error ("no such platform: " ++ name)
            Just p -> return p

#endif

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
        wcnf <- CNF.readFile fname

#ifdef ENABLE_OPENCL
        if optOpenCL opt then do
          platform <- getPlatform (optOpenCLPlatform opt)
          devs <- clGetDeviceIDs platform CL_DEVICE_TYPE_ALL
          dev <-
            if optOpenCLDevice opt < length devs then
              return (devs !! optOpenCLDevice opt)
            else do
              name <- clGetPlatformInfo platform CL_PLATFORM_NAME
              error ("platform " ++ name ++ " has only " ++ show (length devs) ++ " devices")
          context <- clCreateContext [] [dev] print
          solver <- SPCL.newSolver putStrLn context dev
            (CNF.wcnfNumVars wcnf) [(fromIntegral w, clause) | (w,clause) <- CNF.wcnfClauses wcnf]
          -- Rand.withSystemRandom $ SPCL.initializeRandom solver
          print =<< SPCL.propagate solver
          forM_ [1 .. CNF.wcnfNumVars wcnf] $ \v -> do
            prob <- SPCL.getVarProb solver v
            print (v,prob)
          SPCL.deleteSolver solver
#else
        if False then do
          return ()
#endif
        else do
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
