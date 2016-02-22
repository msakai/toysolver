{-# LANGUAGE ScopedTypeVariables, CPP #-}
{-# OPTIONS_GHC -Wall #-}
module Main where

import Control.Concurrent
import System.Environment
import qualified System.Random.MWC as Rand

import qualified ToySolver.SAT.MessagePassing.SurveyPropagation as SP
import qualified ToySolver.Text.MaxSAT as MaxSAT
import ToySolver.Internal.Util (setEncodingChar8)

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif
  [fname] <- getArgs
  Right wcnf <- MaxSAT.parseFile fname
  solver <- SP.newSolver (MaxSAT.numVars wcnf) [(fromIntegral w, clause) | (w,clause) <- MaxSAT.clauses wcnf]
  SP.setNThreads solver =<< getNumCapabilities
  Rand.withSystemRandom $ SP.initializeRandom solver
  print =<< SP.solve solver
