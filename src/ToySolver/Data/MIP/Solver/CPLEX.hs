{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module ToySolver.Data.MIP.Solver.CPLEX
  ( CPLEX (..)
  , cplex
  ) where

import Control.Monad
import Data.Default.Class
import Data.IORef
import qualified Data.Text.Lazy.IO as TLIO
import System.Exit
import System.IO
import System.IO.Temp
import qualified ToySolver.Data.MIP.Base as MIP
import qualified ToySolver.Data.MIP.LPFile as LPFile
import ToySolver.Data.MIP.Solver.Base
import qualified ToySolver.Data.MIP.Solution.CPLEX as CPLEXSol
import ToySolver.Internal.ProcessUtil (runProcessWithOutputCallback)

data CPLEX
  = CPLEX
  { cplexPath :: String
  }

instance Default CPLEX where
  def = cplex

cplex :: CPLEX
cplex = CPLEX "cplex"

instance IsSolver CPLEX IO where
  solve solver opt prob = do
    case LPFile.render def prob of
      Left err -> ioError $ userError err
      Right lp -> do
        withSystemTempFile "cplex.lp" $ \fname1 h1 -> do
          TLIO.hPutStr h1 lp
          hClose h1
          withSystemTempFile "cplex.sol" $ \fname2 h2 -> do
            hClose h2
            isInfeasibleRef <- newIORef False
            let args = []
                input = unlines $
                  (case solveTimeLimit opt of
                          Nothing -> []
                          Just sec -> ["set timelimit ", show sec]) ++
                  [ "read " ++ show fname1
                  , "optimize"
                  , "write " ++ show fname2
                  , "y"
                  , "quit"
                  ]
                onGetLine s = do
                  when (s == "MIP - Integer infeasible.") $ do
                    writeIORef isInfeasibleRef True
                  solveLogger opt s
                onGetErrorLine = solveErrorLogger opt
            exitcode <- runProcessWithOutputCallback (cplexPath solver) args input onGetLine onGetErrorLine
            case exitcode of
              ExitFailure n -> ioError $ userError $ "exit with " ++ show n
              ExitSuccess -> do
                size <- withFile fname2 ReadMode $ hFileSize
                if size == 0 then do
                  isInfeasible <- readIORef isInfeasibleRef
                  if isInfeasible then
                    return def{ MIP.solStatus = Just MIP.StatusInfeasible }
                  else
                    return def
                else
                  CPLEXSol.readFile fname2
