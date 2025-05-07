{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
----------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Solver.SLS.UBCSAT
-- Copyright   :  (c) Masahiro Sakai 2017
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- References:
--
----------------------------------------------------------------------
module ToySolver.SAT.Solver.SLS.UBCSAT
  ( ubcsatBest
  , ubcsatBestFeasible
  , ubcsatMany
  , Options (..)
  ) where

import Control.Exception
import Control.Monad
import Data.Array.IArray
import Data.Char
import Data.Default
import Data.Either
import Data.Function
import Data.List (isSuffixOf, minimumBy)
import Data.Void
import System.Directory
import System.IO
import System.IO.Temp
import System.Process
import Text.Megaparsec hiding (try)
import Text.Megaparsec.Char

import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.SAT.Types as SAT

data Options
  = Options
  { optCommand :: FilePath
  , optTempDir :: Maybe FilePath
  , optProblem :: CNF.WCNF
  , optProblemFile :: Maybe FilePath
  , optVarInit :: [SAT.Lit]
  }

instance Default Options where
  def = Options
        { optCommand = "ubcsat"
        , optTempDir = Nothing
        , optProblem =
            CNF.WCNF
            { CNF.wcnfNumVars    = 0
            , CNF.wcnfNumClauses = 0
            , CNF.wcnfTopCost    = 1
            , CNF.wcnfClauses    = []
            }
        , optProblemFile   = Nothing
        , optVarInit = []
        }

ubcsatBestFeasible :: Options -> IO (Maybe (Integer, SAT.Model))
ubcsatBestFeasible opt = do
  ret <- ubcsatBest opt
  case ret of
    Nothing -> return Nothing
    Just (obj,_) ->
      if obj < CNF.wcnfTopCost (optProblem opt) then
        return ret
      else
        return Nothing

ubcsatBest :: Options -> IO (Maybe (Integer, SAT.Model))
ubcsatBest opt = do
  sols <- ubcsatMany opt
  case sols of
    [] -> return Nothing
    _ -> return $ Just $ minimumBy (compare `on` fst) sols

ubcsatMany :: Options -> IO [(Integer, SAT.Model)]
ubcsatMany opt = do
  dir <- case optTempDir opt of
           Just dir -> return dir
           Nothing -> getTemporaryDirectory

  let f fname
        | null (optVarInit opt) = ubcsat' opt fname Nothing
        | otherwise = do
            withTempFile dir ".txt" $ \varInitFile h -> do
              hSetBinaryMode h True
              hSetBuffering h (BlockBuffering Nothing)
              forM_ (split 10 (optVarInit opt)) $ \xs -> do
                hPutStrLn h $ unwords (map show xs)
              hClose h
              ubcsat' opt fname (Just varInitFile)

  case optProblemFile opt of
    Just fname -> f fname
    Nothing -> do
      withTempFile dir ".wcnf" $ \fname h -> do
        hClose h
        CNF.writeFile fname (optProblem opt)
        f fname

ubcsat' :: Options -> FilePath -> Maybe FilePath -> IO [(Integer, SAT.Model)]
ubcsat' opt fname varInitFile = do
  let wcnf = optProblem opt
  let args =
        [ "-w" | ".wcnf" `isSuffixOf` map toLower fname] ++
        [ "-alg", "irots"
        , "-seed", "0"
        , "-runs", "10"
        , "-cutoff", show (CNF.wcnfNumVars wcnf * 50)
        , "-timeout", show (10 :: Int)
        , "-gtimeout", show (30 :: Int)
        , "-solve"
        , "-r", "bestsol"
        , "-inst", fname
        ] ++
        (case varInitFile of
           Nothing -> []
           Just fname2 -> ["-varinitfile", fname2])
      stdinStr = ""

  putStrLn $ "c Running " ++ show (optCommand opt) ++ " with " ++ show args
  ret <- try $ readProcess (optCommand opt) args stdinStr
  case ret of
    Left (err :: IOError) -> do
      forM_ (lines (show err)) $ \l -> do
        putStr "c " >> putStrLn l
      return []
    Right s -> do
      forM_ (lines s) $ \l -> putStr "c " >> putStrLn l
      return $ scanSolutions (CNF.wcnfNumVars wcnf) s

scanSolutions :: Int -> String -> [(Integer, SAT.Model)]
scanSolutions nv s = rights $ map (parse (solution nv) "") $ lines s

solution :: MonadParsec Void String m => Int -> m (Integer, SAT.Model)
solution nv = do
  skipSome digitChar
  space
  _ <- char '0' <|> char '1'
  space
  obj <- liftM read $ some digitChar
  space
  values <- many ((char '0' >> return False) <|> (char '1' >> return True))
  let m = array (1, nv) (zip [1..] values)
  return (obj, m)


split :: Int -> [a] -> [[a]]
split n = go
  where
    go [] = []
    go xs =
      case splitAt n xs of
        (ys, zs) -> ys : go zs
