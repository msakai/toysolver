{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  toysmt
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Main where

import Control.Applicative
import Control.Monad
import System.Environment
import System.Exit
import System.IO
import Text.ParserCombinators.Parsec
import Smtlib.Parsers.CommandsParsers

import Solver

main :: IO ()
main = do
  [fname] <- getArgs
  ret <- parseFromFile parseSource fname
  case ret of
    Left err -> do
      hPrint stderr err
      exitFailure
    Right source -> do
      solver <- newSolver
      forM_ source $ \cmd -> do
        execCommand solver cmd
