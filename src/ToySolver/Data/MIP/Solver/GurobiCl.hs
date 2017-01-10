{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module ToySolver.Data.MIP.Solver.GurobiCl
  ( GurobiCl (..)
  , gurobiCl
  ) where

import Data.Default.Class
import Data.IORef
import Data.List (isPrefixOf)
import qualified Data.Text.Lazy.IO as TLIO
import System.Exit
import System.IO
import System.IO.Temp
import qualified ToySolver.Data.MIP.Base as MIP
import qualified ToySolver.Data.MIP.LPFile as LPFile
import ToySolver.Data.MIP.Solver.Base
import qualified ToySolver.Data.MIP.Solution.Gurobi as GurobiSol
import ToySolver.Internal.ProcessUtil (runProcessWithOutputCallback)

data GurobiCl
  = GurobiCl
  { gurobiClPath :: String
  }

instance Default GurobiCl where
  def = gurobiCl

gurobiCl :: GurobiCl
gurobiCl = GurobiCl "gurobi_cl"

instance IsSolver GurobiCl IO where
  solve solver opt prob = do
    case LPFile.render def prob of
      Left err -> ioError $ userError err
      Right lp -> do
        withSystemTempFile "gurobi.lp" $ \fname1 h1 -> do
          TLIO.hPutStr h1 lp
          hClose h1
          withSystemTempFile "gurobi.sol" $ \fname2 h2 -> do
            hClose h2
            statusRef <- newIORef Nothing
            let args = ["ResultFile=" ++ fname2]
                    ++ (case solveTimeLimit opt of
                          Nothing -> []
                          Just sec -> ["TimeLimit=" ++ show sec])
                    ++ [fname1]
                onGetLine s = do
                  case s of
                    "Time limit reached" -> writeIORef statusRef (Just MIP.StatusInterrupted)
                    "Model is unbounded" -> writeIORef statusRef (Just MIP.StatusUnbounded)
                    "Model is infeasible" -> writeIORef statusRef (Just MIP.StatusInfeasible)
                    _ | isPrefixOf "Optimal solution found" s -> writeIORef statusRef (Just MIP.StatusOptimal)
                    _ -> return ()
                  putStrLn s
                onGetErrorLine s = putStrLn $ "err: " ++ s
            exitcode <- runProcessWithOutputCallback (gurobiClPath solver) args "" onGetLine onGetErrorLine
            case exitcode of
              ExitFailure n -> ioError $ userError $ "exit with " ++ show n
              ExitSuccess -> do
                status <- readIORef statusRef
                sol <- GurobiSol.readFile fname2
                return $ sol{ MIP.solStatus = status }
