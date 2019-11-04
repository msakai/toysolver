{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Combinatorial.HittingSet.HTCBDD
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Wrapper for htcbdd command.
--
-- * HTC-BDD: Hypergraph Transversal Computation with Binary Decision Diagrams
--   <http://kuma-san.net/htcbdd.html>
--
-----------------------------------------------------------------------------
module ToySolver.Combinatorial.HittingSet.HTCBDD
  ( Options (..)
  , Method (..)
  , Failure (..)
  , minimalHittingSets
  ) where

import Control.Exception (Exception, throwIO)
import Control.Monad
import Data.Default.Class
import Data.Array.Unboxed
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
  { optHTCBDDCommand  :: FilePath
  , optMethod         :: Method
  , optOnGetLine      :: String -> IO ()
  , optOnGetErrorLine :: String -> IO ()
  }

data Method
  = MethodToda
  | MethodKnuth
  deriving (Eq, Ord, Show)

instance Default Method where
  def = MethodToda

instance Default Options where
  def =
    Options
    { optHTCBDDCommand  = "htcbdd"
    , optMethod         = def
    , optOnGetLine      = \_ -> return ()
    , optOnGetErrorLine = \_ -> return ()
    }

data Failure = Failure !Int
  deriving (Show, Typeable)

instance Exception Failure

minimalHittingSets :: Options -> Set IntSet -> IO (Set IntSet)
minimalHittingSets opt es = do
  withSystemTempFile "htcbdd-input.dat" $ \fname1 h1 -> do
    forM_ (Set.toList es) $ \e -> do
      hPutStrLn h1 $ unwords [show (encTable IntMap.! v) | v <- IntSet.toList e]
    hClose h1
    withSystemTempFile "htcbdd-out.dat" $ \fname2 h2 -> do
      hClose h2
      execHTCBDD opt fname1 fname2
      s <- readFile fname2
      return $ Set.fromList $ map (IntSet.fromList . map ((decTable !) . read) . words) $ lines s
  where
    vs :: IntSet
    vs = IntSet.unions (Set.toList es)

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
