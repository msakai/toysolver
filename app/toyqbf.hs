{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  toyqbf
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-----------------------------------------------------------------------------

module Main where

import Control.Monad
import Data.Char
import qualified Data.IntSet as IntSet
import Data.List (sortBy)
import Data.Ord
import Data.Version
import Options.Applicative
import System.Exit
import System.IO

import ToySolver.Data.Boolean
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.QBF as QBF
import ToySolver.Internal.Util (setEncodingChar8)
import ToySolver.Version

data Options
  = Options
  { optAlgorithm :: String
  , optInput :: FilePath
  }

optionsParser :: Parser Options
optionsParser = Options
  <$> algorithmOption
  <*> fileInput
  where
    fileInput :: Parser FilePath
    fileInput = argument str (metavar "FILE")

    algorithmOption :: Parser String
    algorithmOption = strOption
      $  long "algorithm"
      <> metavar "STR"
      <> help "Algorithm: naive, cegar, cegar-incremental, qe"
      <> value "cegar-incremental"
      <> showDefaultWith id

parserInfo :: ParserInfo Options
parserInfo = info (helper <*> versionOption <*> optionsParser)
  $  fullDesc
  <> header "toyqbf - an QBF solver"
  where
    versionOption :: Parser (a -> a)
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

  ret <- CNF.parseFile (optInput opt)
  case ret of
    Left err -> hPutStrLn stderr err >> exitFailure
    Right qdimacs -> do
      let nv = CNF.qdimacsNumVars qdimacs
          nc = CNF.qdimacsNumClauses qdimacs
          prefix' = QBF.quantifyFreeVariables nv [(q, IntSet.fromList xs) | (q,xs) <- CNF.qdimacsPrefix qdimacs]
          matrix' = andB [orB [if lit > 0 then QBF.litToMatrix lit else notB (QBF.litToMatrix (abs lit)) | lit <- CNF.unpackClause clause] | clause <- CNF.qdimacsMatrix qdimacs]
      (ans, certificate) <-
        case map toLower (optAlgorithm opt) of
          "naive" -> QBF.solveNaive nv prefix' matrix'
          "cegar" -> QBF.solveCEGAR nv prefix' matrix'
          "cegar-incremental" -> QBF.solveCEGARIncremental nv prefix' matrix'
          "qe" -> QBF.solveQE nv prefix' matrix'
          _ -> do
            putStrLn $ "c unknown --algorithm option: " ++ show (optAlgorithm opt)
            putStrLn $ "s cnf 0 " ++ show nv ++ " " ++ show nc
            exitFailure
      putStrLn $ "s cnf " ++ (if ans then "1" else "0") ++ " " ++ show nv ++ " " ++ show nc
      case certificate of
        Nothing -> return ()
        Just lits -> do
          forM_ (sortBy (comparing abs) (IntSet.toList lits)) $ \lit -> do
            putStrLn ("V " ++ show lit)
      if ans then
        exitWith (ExitFailure 10)
      else
        exitWith (ExitFailure 20)
