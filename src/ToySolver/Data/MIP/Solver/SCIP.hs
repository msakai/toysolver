{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module ToySolver.Data.MIP.Solver.SCIP
  ( SCIP (..)
  , scip
  ) where

import Data.Default.Class
import qualified Data.Text.Lazy.IO as TLIO
import System.Exit
import System.IO
import System.IO.Temp
import qualified ToySolver.Data.MIP.LPFile as LPFile
import ToySolver.Data.MIP.Solver.Base
import qualified ToySolver.Data.MIP.Solution.SCIP as ScipSol
import ToySolver.Internal.ProcessUtil (runProcessWithOutputCallback)

data SCIP
  = SCIP
  { scipPath :: String
  }

instance Default SCIP where
  def = scip

scip :: SCIP
scip = SCIP "scip"

instance IsSolver SCIP IO where
  solve solver opt prob = do
    case LPFile.render def prob of
      Left err -> ioError $ userError err
      Right lp -> do
        withSystemTempFile "scip.lp" $ \fname1 h1 -> do
          TLIO.hPutStr h1 lp
          hClose h1
          withSystemTempFile "scip.sol" $ \fname2 h2 -> do
            hClose h2
            let args = [ "-c", "read " ++ show fname1 ]
                    ++ (case solveTimeLimit opt of
                          Nothing -> []
                          Just sec -> ["-c", "set limits time " ++ show sec])
                    ++ [ "-c", "optimize"
                       , "-c", "write solution " ++ show fname2
                       , "-c", "quit"
                       ]
                onGetLine = solveLogger opt
                onGetErrorLine = solveErrorLogger opt
            exitcode <- runProcessWithOutputCallback (scipPath solver) args "" onGetLine onGetErrorLine
            case exitcode of
              ExitFailure n -> ioError $ userError $ "exit with " ++ show n
              ExitSuccess -> ScipSol.readFile fname2
