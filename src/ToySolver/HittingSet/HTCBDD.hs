{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.HittingSet.HTCBDD
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (DeriveDataTypeable)
--
-- Wrapper for htcbdd command.
--
-- * HTC-BDD: Hypergraph Transversal Computation with Binary Decision Diagrams
--   <http://kuma-san.net/htcbdd.html>
--
-----------------------------------------------------------------------------
module ToySolver.HittingSet.HTCBDD
  ( Options (..)
  , Method (..)
  , Failure (..)
  , defaultOptions
  , minimalHittingSets
  ) where

import Control.Exception (Exception, throwIO)
import Control.Monad
import Data.Array.Unboxed
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.List
import Data.Typeable
import System.Exit
import System.IO
import System.IO.Temp
import ToySolver.Internal.ProcessUtil (runProcessWithOutputCallback)

type Vertex = Int
type HyperEdge = [Vertex]
type HittingSet = [Vertex]

data Options
  = Options
  { optHTCBDDCommand  :: FilePath
  , optMethod         :: Method
  , optOnGetLine      :: String -> IO ()
  , optOnGetErrorLine :: String -> IO ()
  }

data Method
  = MethodToda
  | MethodKnuth
  deriving (Eq, Ord, Show)

defaultOptions :: Options
defaultOptions =
  Options
  { optHTCBDDCommand  = "htcbdd"
  , optMethod         = MethodToda
  , optOnGetLine      = \_ -> return ()
  , optOnGetErrorLine = \_ -> return ()
  }

data Failure = Failure !Int
  deriving (Show, Typeable)

instance Exception Failure

minimalHittingSets :: Options -> [HyperEdge] -> IO [HittingSet]
minimalHittingSets opt es = do
  withSystemTempFile "htcbdd-input.dat" $ \fname1 h1 -> do
    forM_ es' $ \e -> do
      hPutStrLn h1 $ intercalate " " [show (encTable IntMap.! v) | v <- IntSet.toList e]
    hClose h1
    withSystemTempFile "htcbdd-out.dat" $ \fname2 h2 -> do
      hClose h2
      execHTCBDD opt fname1 fname2
      s <- readFile fname2
      return $ map (map ((decTable !) . read) . words) $ lines s
  where
    es' :: [IntSet]
    es' = map IntSet.fromList es

    vs :: IntSet
    vs = IntSet.unions es'

    nv :: Int
    nv = IntSet.size vs

    encTable :: IntMap Int
    encTable = IntMap.fromList (zip (IntSet.toList vs) [1..nv])

    decTable :: UArray Int Int
    decTable = array (1,nv) (zip [1..nv] (IntSet.toList vs))

execHTCBDD :: Options -> FilePath -> FilePath -> IO ()
execHTCBDD opt inputFile outputFile = do
  let args = ["-k" | optMethod opt == MethodKnuth] ++ [inputFile, outputFile]
  exitcode <- runProcessWithOutputCallback (optHTCBDDCommand opt) args "" (optOnGetLine opt) (optOnGetErrorLine opt)
  case exitcode of
    ExitFailure n -> throwIO $ Failure n
    ExitSuccess -> return ()
