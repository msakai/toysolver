{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module ToySolver.Data.MIP.Solver.Glpsol
  ( Glpsol (..)
  , glpsol
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
import qualified ToySolver.Data.MIP.Solution.GLPK as GLPKSol
import ToySolver.Internal.ProcessUtil (runProcessWithOutputCallback)

data Glpsol
  = Glpsol
  { glpsolPath :: String
  }

instance Default Glpsol where
  def = glpsol

glpsol :: Glpsol
glpsol = Glpsol "glpsol"

instance IsSolver Glpsol IO where
  solve solver opt prob = do
    case LPFile.render def prob of
      Left err -> ioError $ userError err
      Right lp -> do
        withSystemTempFile "glpsol.lp" $ \fname1 h1 -> do
          TLIO.hPutStr h1 lp
          hClose h1
          withSystemTempFile "glpsol.sol" $ \fname2 h2 -> do
            hClose h2
            isUnboundedRef <- newIORef False
            let args = ["--lp", fname1, "-o", fname2] ++
                       (case solveTimeLimit opt of
                          Nothing -> []
                          Just sec -> ["--tmlim", show (max 1 (floor sec) :: Int)])
                onGetLine s = do
                  when (s == "LP HAS UNBOUNDED PRIMAL SOLUTION") $ do
                    writeIORef isUnboundedRef True
                  putStrLn s
                onGetErrorLine s = putStrLn $ "err: " ++ s
            exitcode <- runProcessWithOutputCallback (glpsolPath solver) args "" onGetLine onGetErrorLine
            case exitcode of
              ExitFailure n -> ioError $ userError $ "exit with " ++ show n
              ExitSuccess -> do
                sol <- GLPKSol.readFile fname2
                isUnbounded <- readIORef isUnboundedRef
                if isUnbounded && MIP.solStatus sol == Nothing then
                  return $ sol{ MIP.solStatus = Just MIP.StatusInfeasibleOrUnbounded }
                else
                  return sol
