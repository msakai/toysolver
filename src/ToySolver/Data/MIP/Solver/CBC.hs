{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.MIP.Solver.CBC
-- Copyright   :  (c) Masahiro Sakai 2017
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Data.MIP.Solver.CBC
  ( CBC (..)
  , cbc
  ) where

import Data.Default.Class
import qualified Data.Text.Lazy.IO as TLIO
import System.Exit
import System.IO
import System.IO.Temp
import qualified ToySolver.Data.MIP.Base as MIP
import qualified ToySolver.Data.MIP.LPFile as LPFile
import ToySolver.Data.MIP.Solver.Base
import qualified ToySolver.Data.MIP.Solution.CBC as CBCSol
import ToySolver.Internal.ProcessUtil (runProcessWithOutputCallback)

data CBC
  = CBC
  { cbcPath :: String
  }

instance Default CBC where
  def = cbc

cbc :: CBC
cbc = CBC "cbc"

instance IsSolver CBC IO where
  solve solver opt prob = do
    case LPFile.render def prob of
      Left err -> ioError $ userError err
      Right lp -> do
        withSystemTempFile "cbc.lp" $ \fname1 h1 -> do
          TLIO.hPutStr h1 lp
          hClose h1
          withSystemTempFile "cbc.sol" $ \fname2 h2 -> do
            hClose h2
            let args = [fname1]
                    ++ (case solveTimeLimit opt of
                          Nothing -> []
                          Just sec -> ["sec", show sec])
                    ++ ["solve", "solu", fname2]
                onGetLine = solveLogger opt
                onGetErrorLine = solveErrorLogger opt
            exitcode <- runProcessWithOutputCallback (cbcPath solver) args "" onGetLine onGetErrorLine
            case exitcode of
              ExitFailure n -> ioError $ userError $ "exit with " ++ show n
              ExitSuccess -> do
                sol <- CBCSol.readFile fname2
                if MIP.objDir (MIP.objectiveFunction prob) == MIP.OptMax then
                  return $ sol{ MIP.solObjectiveValue = fmap negate (MIP.solObjectiveValue sol) }
                else
                  return sol
