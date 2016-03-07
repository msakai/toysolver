{-# LANGUAGE ScopedTypeVariables #-}
import Control.Exception
import Control.Monad
import Control.Parallel.OpenCL
import System.Environment
import qualified ToySolver.Text.MaxSAT as MaxSAT
import qualified ToySolver.SAT.MessagePassing.SurveyPropagation.OpenCL as SP

main = do
  ids@(platform:_) <- clGetPlatformIDs
  (dev:_) <- clGetDeviceIDs platform CL_DEVICE_TYPE_ALL
  context <- clCreateContext [] [dev] print

  handle (\(e::SomeException) -> print e) $ do
    [fname] <- getArgs
    Right wcnf <- MaxSAT.parseFile fname
    solver <- SP.newSolver putStrLn context dev
      (MaxSAT.numVars wcnf) [(fromIntegral w, clause) | (w,clause) <- MaxSAT.clauses wcnf]
    -- Rand.withSystemRandom $ SP.initializeRandom solver
    print =<< SP.propagate solver
    forM [1 .. MaxSAT.numVars wcnf] $ \v -> do
      prob <- SP.getVarProb solver v
      print (v,prob)
    SP.deleteSolver solver

  return ()
