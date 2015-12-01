{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  toysmt
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (CPP)
--
-----------------------------------------------------------------------------
module Main where

import Control.Applicative ((<*))
import Control.Monad
import Control.Monad.Trans
import Data.Default.Class
import Data.Version
import System.Console.GetOpt
#ifdef USE_HASKELINE_PACKAGE
import qualified System.Console.Haskeline as Haskeline
#endif
import System.Environment
import System.Exit
import System.IO
import Text.Parsec
import Text.Parsec.String

import ToySolver.Version

import Smtlib.Parsers.CommandsParsers
import Solver

data Mode
  = ModeHelp
  | ModeVersion
  | ModeInteractive
  deriving (Eq, Ord, Bounded, Enum)

data Options
  = Options
  { optMode :: Maybe Mode
  , optInteractive :: Bool
  }

instance Default Options where
  def =
    Options
    { optMode = Nothing
    , optInteractive = False 
    }

options :: [OptDescr (Options -> Options)]
options =
    [ Option ['h'] ["help"]   (NoArg (\opt -> opt{ optMode = Just ModeHelp   })) "show help"
    , Option [] ["version"]   (NoArg (\opt -> opt{ optMode = Just ModeVersion})) "show version"
    , Option [] ["interactive"] (NoArg (\opt -> opt{ optMode = Just ModeInteractive })) "force interactive mode"
    ]

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (_,_,errs@(_:_)) -> do
      mapM_ putStrLn errs
      exitFailure

    (o,args2,[]) -> do
      let opt = foldl (flip id) def o
      case optMode opt of
        Just ModeHelp -> showHelp stdout
        Just ModeVersion -> hPutStrLn stdout (showVersion version)
        Just ModeInteractive -> do
          solver <- newSolver
          mapM_ (loadFile solver) args2
          repl solver          
        Nothing -> do
          solver <- newSolver
          if null args2 then
            repl solver
          else
            mapM_ (loadFile solver) args2

loadFile :: Solver -> FilePath -> IO ()
loadFile solver fname = do
  ret <- parseFromFile (parseSource <* eof) fname
  case ret of
    Left err -> do
      hPrint stderr err
      exitFailure
    Right source -> do
      forM_ source $ \cmd -> do
        execCommand solver cmd

repl :: Solver -> IO ()
repl solver = do
#ifdef USE_HASKELINE_PACKAGE
  replHaskeline solver
#else
  replSimple solver
#endif

replSimple :: Solver -> IO ()
replSimple solver = do
  hSetBuffering stdin LineBuffering
  forever $ do
    putStr "toysmt> "
    hFlush stdout
    s <- getLine
    case parse (spaces >> parseCommand <* eof) "<stdin>" s of
      Left err -> do
        hPrint stderr err
      Right cmd -> do
        execCommand solver cmd

#ifdef USE_HASKELINE_PACKAGE

replHaskeline :: Solver -> IO ()
replHaskeline solver = Haskeline.runInputT Haskeline.defaultSettings $ forever $ do
  m <- Haskeline.getInputLine "toysmt> "
  case m of
    Nothing -> return ()
    Just s -> do
      case parse (spaces >> parseCommand) "<stdin>" s of
        Left err -> do
          lift $ hPrint stderr err
        Right cmd -> do
          lift $ execCommand solver cmd

#endif

showHelp :: Handle -> IO ()
showHelp h = hPutStrLn h (usageInfo header options)

header :: String
header = unlines
  [ "Usage:"
  , "  toysmt [OPTION]... [file.smt2]"
  , ""
  , "Options:"
  ]
