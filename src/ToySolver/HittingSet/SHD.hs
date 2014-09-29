{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.HittingSet.SHD
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (DeriveDataTypeable)
-- 
-- Wrapper for shd command.
--
-- * Hypergraph Dualization Repository
--   <http://research.nii.ac.jp/~uno/dualization.html>
--
-----------------------------------------------------------------------------
module ToySolver.HittingSet.SHD
  ( Options (..)
  , Failure (..)
  , defaultOptions
  , minimalHittingSets
  ) where

import Control.Exception (Exception, throwIO)
import Control.Monad
import Data.Array.Unboxed
import Data.Default.Class
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
  { optSHDCommand     :: FilePath
  , optSHDArgs        :: [String]
  , optOnGetLine      :: String -> IO ()
  , optOnGetErrorLine :: String -> IO ()
  }

instance Default Options where
  def = defaultOptions

defaultOptions :: Options
defaultOptions =
  Options
  { optSHDCommand     = "shd"
  , optSHDArgs        = ["0"]
  , optOnGetLine      = \_ -> return ()
  , optOnGetErrorLine = \_ -> return ()
  }

data Failure = Failure !Int
  deriving (Show, Typeable)

instance Exception Failure

minimalHittingSets :: Options -> [HyperEdge] -> IO [HittingSet]
minimalHittingSets opt es = do
  withSystemTempFile "shd-input.dat" $ \fname1 h1 -> do
    forM_ es' $ \e -> do
      hPutStrLn h1 $ intercalate " " [show (encTable IntMap.! v) | v <- IntSet.toList e]
    hClose h1
    withSystemTempFile "shd-out.dat" $ \fname2 h2 -> do
      hClose h2
      execSHD opt fname1 fname2
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
    encTable = IntMap.fromList (zip (IntSet.toList vs) [0..nv-1])

    decTable :: UArray Int Int
    decTable = array (0,nv-1) (zip [0..nv-1] (IntSet.toList vs))

execSHD :: Options -> FilePath -> FilePath -> IO ()
execSHD opt inputFile outputFile = do
  let args = optSHDArgs opt ++ [inputFile, outputFile]
  exitcode <- runProcessWithOutputCallback (optSHDCommand opt) args "" (optOnGetLine opt) (optOnGetErrorLine opt)
  case exitcode of
    ExitFailure n -> throwIO $ Failure n
    ExitSuccess -> return ()
