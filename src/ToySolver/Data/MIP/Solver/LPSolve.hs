{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module ToySolver.Data.MIP.Solver.LPSolve
  ( LPSolve (..)
  , lpSolve
  ) where

import Control.Monad
import Data.Default.Class
import Data.IORef
import Data.List (stripPrefix)
import qualified Data.Map as Map
import Data.String
import qualified Data.Text.Lazy.IO as TLIO
import System.Exit
import System.IO
import System.IO.Temp
import qualified ToySolver.Data.MIP.Base as MIP
import qualified ToySolver.Data.MIP.MPSFile as MPSFile
import ToySolver.Data.MIP.Solver.Base
import ToySolver.Internal.ProcessUtil (runProcessWithOutputCallback)

data LPSolve
  = LPSolve
  { lpSolvePath :: String
  }

instance Default LPSolve where
  def = lpSolve

lpSolve :: LPSolve
lpSolve = LPSolve "lp_solve"

instance IsSolver LPSolve IO where
  solve solver opt prob = do
    case MPSFile.render def prob of
      Left err -> ioError $ userError err
      Right lp -> do
        withSystemTempFile "lp_solve.mps" $ \fname1 h1 -> do
          TLIO.hPutStr h1 lp
          hClose h1
          objRef <- newIORef Nothing
          solRef <- newIORef []
          flagRef <- newIORef False
          let args = (case solveTimeLimit opt of
                        Nothing -> []
                        Just sec -> ["-timeout", show sec])
                  ++ ["-fmps", fname1]
              onGetLine s = do
                case s of
                  "Actual values of the variables:" -> writeIORef flagRef True
                  _ | Just v <- stripPrefix "Value of objective function: " s -> do
                    writeIORef objRef (Just (read v))
                  _ -> do
                    flag <- readIORef flagRef
                    when flag $ do
                      case words s of
                        [var,val] -> modifyIORef solRef ((fromString var, read val) :)
                        _ -> return ()
                    return ()
                solveLogger opt s
              onGetErrorLine = solveErrorLogger opt
          exitcode <- runProcessWithOutputCallback (lpSolvePath solver) args "" onGetLine onGetErrorLine
          status <-
            case exitcode of
              ExitSuccess      -> return (Just MIP.StatusOptimal)
              ExitFailure (-2) -> return (Just MIP.StatusInterrupted) -- NOMEMORY
              ExitFailure 1    -> return (Just MIP.StatusInterrupted) -- SUBOPTIMAL
              ExitFailure 2    -> return (Just MIP.StatusInfeasible)  -- INFEASIBLE
              ExitFailure 3    -> return (Just MIP.StatusUnbounded)   -- UNBOUNDED
              ExitFailure 4    -> return Nothing                      -- DEGENERATE
              ExitFailure 5    -> return Nothing                      -- NUMFAILURE
              ExitFailure 6    -> return (Just MIP.StatusInterrupted) -- USERABORT
              ExitFailure 7    -> return (Just MIP.StatusInterrupted) -- TIMEOUT
              ExitFailure 9    -> return (Just MIP.StatusOptimal)     -- PRESOLVED
              ExitFailure 25   -> return (Just MIP.StatusInterrupted) -- NUMFAILURE
              ExitFailure n    -> ioError $ userError $ "unknown exit code: " ++ show n
          obj <- readIORef objRef
          sol <- readIORef solRef
          return $
            MIP.Solution
            { MIP.solStatus = status
            , MIP.solObjectiveValue = obj
            , MIP.solVariables = Map.fromList sol
            }
