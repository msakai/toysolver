{-# LANGUAGE ScopedTypeVariables, CPP #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  toyqbf
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (ScopedTypeVariables, CPP)
--
-----------------------------------------------------------------------------

module Main where

import Control.Monad
import Data.Char
import Data.Default.Class
import qualified Data.IntSet as IntSet
import Data.List
import Data.Ord
import Data.Version
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO

import ToySolver.Data.Boolean
import qualified ToySolver.QBF as QBF
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin
import qualified ToySolver.Text.QDimacs as QDimacs
import ToySolver.Internal.Util (setEncodingChar8)
import ToySolver.Version

data Mode
  = ModeHelp
  | ModeVersion
  deriving (Eq, Ord, Bounded, Enum)

data Options
  = Options
  { optMode :: Maybe Mode
  , optAlgorithm :: String
  }

instance Default Options where
  def =
    Options
    { optMode = Nothing
    , optAlgorithm = "cegar-incremental"
    }

options :: [OptDescr (Options -> Options)]
options =
    [ Option ['h'] ["help"]   (NoArg (\opt -> opt{ optMode = Just ModeHelp   })) "show help"
    , Option [] ["version"]   (NoArg (\opt -> opt{ optMode = Just ModeVersion})) "show version"
    , Option [] ["algorithm"]
        (ReqArg (\val opt -> opt{ optAlgorithm = val }) "<str>")
        "Algorithm: naive, cegar, cegar-incremental (default)"
    ]

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif

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
        Nothing -> do
          case args2 of
            [fname] -> do
              ret <- QDimacs.parseFile fname
              case ret of
                Left err -> hPutStrLn stderr err >> exitFailure
                Right qdimacs -> do
                  let nv = QDimacs.numVars qdimacs
                      nc = QDimacs.numClauses qdimacs
                      prefix' = QBF.quantifyFreeVariables nv [(q, IntSet.fromList xs) | (q,xs) <- QDimacs.prefix qdimacs]
                      matrix' = andB [orB [if lit > 0 then Tseitin.Atom lit else notB (Tseitin.Atom (abs lit)) | lit <- clause] | clause <- QDimacs.matrix qdimacs]
                  (ans, certificate) <-
                    case map toLower (optAlgorithm opt) of
                      "naive" -> QBF.solveNaive nv prefix' matrix'
                      "cegar" -> QBF.solveCEGAR nv prefix' matrix'
                      "cegar-incremental" -> QBF.solveCEGARIncremental nv prefix' matrix'
                      _ -> do
                        putStrLn $ "c unknown --algorithm option: " ++ show (optAlgorithm opt)
                        putStrLn $ "s cnf 0 " ++ show nv ++ " " ++ show nc
                        exitFailure
                  putStrLn $ "s cnf " ++ (if ans then "1" else "-1") ++ " " ++ show nv ++ " " ++ show nc
                  case certificate of
                    Nothing -> return ()
                    Just lits -> do
                      forM_ (sortBy (comparing abs) (IntSet.toList lits)) $ \lit -> do
                        putStrLn ("V " ++ show lit)
                  if ans then
                    exitWith (ExitFailure 10)
                  else
                    exitWith (ExitFailure 20)
            _ -> showHelp stderr >> exitFailure

showHelp :: Handle -> IO ()
showHelp h = hPutStrLn h (usageInfo header options)

header :: String
header = unlines
  [ "Usage:"
  , "  toyqbf [OPTION]... [file.qdimacs]"
  , "  toyqbf [OPTION]... [file.cnf]"
  , ""
  , "Options:"
  ]
