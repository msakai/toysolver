{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
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

import Data.Version
import Options.Applicative hiding (Parser)
import qualified Options.Applicative as Opt
import Control.Monad (when)
import qualified Data.Text.IO as T
#ifdef USE_HASKELINE_PACKAGE
import Control.Monad.IO.Class (liftIO)
import Data.Text (Text)
import qualified Data.Text as T
import qualified System.Console.Haskeline as Haskeline
import Language.SMTLIB.Parser (frameCommand, Result (..))
#endif
import Language.SMTLIB.Reader.Handle (newHandleReader, readCommand)
import System.Exit
import System.IO

import Language.SMTLIB (errorBundlePretty)
import Language.SMTLIB.Parser (parseScript')

import ToySolver.Version
-- 'noAnn' is re-exported by ToySolver.SMT.SMTLIB2Solver (via Language.SMTLIB.Syntax).
import ToySolver.SMT.SMTLIB2Solver
#ifdef FORCE_CHAR8
import ToySolver.Internal.Util (setEncodingChar8)
#endif

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
  txt <- T.readFile fname
  case parseScript' fname txt of
    Left err -> do
      hPutStr stderr (errorBundlePretty err)
      exitFailure
    Right script -> do
      mapM_ (execCommand solver) script

repl :: Solver -> IO ()
repl solver = do
  -- Use the interactive frontend (prompt, and line editing via haskeline if
  -- available) only when stdin is connected to a terminal. When stdin is a pipe
  -- or a regular file, toysmt is typically driven by another program over the
  -- SMT-LIB protocol; in that case we suppress the prompt so that it does not
  -- pollute the response stream on stdout, and we avoid haskeline entirely.
  tty <- hIsTerminalDevice stdin
#ifdef USE_HASKELINE_PACKAGE
  if tty then
    replHaskeline solver
  else
    replSimple False solver
#else
  replSimple tty solver
#endif

replSimple :: Bool -> Solver -> IO ()
replSimple showPrompt solver = do
  hSetBuffering stdin LineBuffering
  hr <- newHandleReader stdin
  let loop = do
        when showPrompt $ do
          putStr "toysmt> "
          hFlush stdout
        r <- readCommand hr
        case r of
          Left err -> do
            hPutStrLn stderr err
            loop
          Right Nothing -> return ()
          Right (Just cmd) -> do
            execCommand solver (noAnn cmd)
            loop
  loop

#ifdef USE_HASKELINE_PACKAGE

replHaskeline :: Solver -> IO ()
replHaskeline solver = Haskeline.runInputT Haskeline.defaultSettings $ loop T.empty
  where
    loop :: Text -> Haskeline.InputT IO ()
    loop buf = do
      let prompt = if T.null (T.strip buf) then "toysmt> " else "... "
      m <- Haskeline.getInputLine prompt
      case m of
        Nothing -> return ()
        Just s -> process (buf <> T.pack s <> "\n")

    process :: Text -> Haskeline.InputT IO ()
    process buf =
      case frameCommand buf of
        Partial _ -> loop buf  -- incomplete command: prompt for more input
        Done (Right cmd) rest -> do
          liftIO $ execCommand solver (noAnn cmd)
          continue rest
        Done (Left err) rest -> do
          liftIO $ hPutStr stderr (errorBundlePretty err)
          continue rest
        Failed err rest -> do
          liftIO $ hPutStrLn stderr ("framing error: " ++ show err)
          continue rest

    continue :: Text -> Haskeline.InputT IO ()
    continue rest
      | T.null (T.strip rest) = loop T.empty
      | otherwise             = process rest

#endif
