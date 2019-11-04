{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Combinatorial.HittingSet.SHD
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Wrapper for shd command.
--
-- * Hypergraph Dualization Repository
--   <http://research.nii.ac.jp/~uno/dualization.html>
--
-----------------------------------------------------------------------------
module ToySolver.Combinatorial.HittingSet.SHD
  ( Options (..)
  , Failure (..)
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
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import System.Exit
import System.IO
import System.IO.Temp
import ToySolver.Internal.ProcessUtil (runProcessWithOutputCallback)

-- | Options for solving.
--
-- The default option can be obtained by 'def'.
data Options
  = Options
  { optSHDCommand     :: FilePath
  , optSHDArgs        :: [String]
  , optOnGetLine      :: String -> IO ()
  , optOnGetErrorLine :: String -> IO ()
  }

instance Default Options where
  def =
    Options
    { optSHDCommand     = "shd"
    , optSHDArgs        = ["0"]
    , optOnGetLine      = \_ -> return ()
    , optOnGetErrorLine = \_ -> return ()
    }

data Failure = Failure !Int
  deriving (Show, Typeable)

instance Exception Failure

minimalHittingSets :: Options -> Set IntSet -> IO (Set IntSet)
minimalHittingSets opt es = do
  withSystemTempFile "shd-input.dat" $ \fname1 h1 -> do
    forM_ (Set.toList es) $ \e -> do
      hPutStrLn h1 $ unwords [show (encTable IntMap.! v) | v <- IntSet.toList e]
    hClose h1
    withSystemTempFile "shd-out.dat" $ \fname2 h2 -> do
      hClose h2
      execSHD opt fname1 fname2
      s <- readFile fname2
      return $ Set.fromList $ map (IntSet.fromList . map ((decTable !) . read) . words) $ lines s
  where
    vs :: IntSet
    vs = IntSet.unions (Set.toList es)

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
