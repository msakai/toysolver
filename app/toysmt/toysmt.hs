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
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module Main where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
#if !MIN_VERSION_base(4,11,0)
import Data.Monoid
#endif
import Data.Version
import Options.Applicative hiding (Parser)
import qualified Options.Applicative as Opt
#ifdef USE_HASKELINE_PACKAGE
import qualified System.Console.Haskeline as Haskeline
#endif
import System.Exit
import System.IO
import Text.Parsec hiding (many)
import Text.Parsec.String

import Smtlib.Parsers.CommandsParsers

import ToySolver.Version
import ToySolver.SMT.SMTLIB2Solver
import ToySolver.Internal.Util (setEncodingChar8)

data Mode
  = ModeHelp
  | ModeVersion
  | ModeInteractive
  deriving (Eq, Ord, Bounded, Enum)

data Options
  = Options
  { optInteractive :: Bool
  , optFiles :: [FilePath]
  }

optionsParser :: Opt.Parser Options
optionsParser = Options
  <$> interactiveOption
  <*> fileArgs
  where
    interactiveOption :: Opt.Parser Bool
    interactiveOption = switch
      $  long "interactive"
      <> help "force interactive mode"

    fileArgs :: Opt.Parser [FilePath]
    fileArgs = many $ strArgument $ metavar "FILE"

parserInfo :: ParserInfo Options
parserInfo = info (helper <*> versionOption <*> optionsParser)
  $  fullDesc
  <> header "toysmt - a SMT solver"
  where
    versionOption :: Opt.Parser (a -> a)
    versionOption = infoOption (showVersion version)
      $  hidden
      <> long "version"
      <> help "Show version"

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif
  opt <- execParser parserInfo
  solver <- newSolver
  if optInteractive opt then do
    mapM_ (loadFile solver) (optFiles opt)
    repl solver
  else do
    if null (optFiles opt) then
      repl solver
    else
      mapM_ (loadFile solver) (optFiles opt)

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
