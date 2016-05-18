{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
module UBCSAT
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
import Data.List
import System.Directory
import System.IO
import System.IO.Temp
import System.Process
import Text.Megaparsec hiding (try)
import Text.Megaparsec.String

import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.Text.MaxSAT as MaxSAT

data Options
  = Options
  { optCommand :: FilePath
  , optTempDir :: Maybe FilePath
  , optProblem :: MaxSAT.WCNF
  , optProblemFile :: Maybe FilePath
  , optVarInit :: [SAT.Lit]
  }

instance Default Options where
  def = Options
        { optCommand = "ubcsat"
        , optTempDir = Nothing
        , optProblem =
            MaxSAT.WCNF
            { MaxSAT.numVars    = 0
            , MaxSAT.numClauses = 0
            , MaxSAT.topCost    = 1
            , MaxSAT.clauses    = []
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
      if obj < MaxSAT.topCost (optProblem opt) then
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
                hPutStrLn h $ intercalate " "  (map show xs)
              hClose h
              ubcsat' opt fname (Just varInitFile)

  case optProblemFile opt of
    Just fname -> f fname
    Nothing -> do
      withTempFile dir ".wcnf" $ \fname h -> do
        hSetBinaryMode h True
        hSetBuffering h (BlockBuffering Nothing)
        MaxSAT.hPutWCNF h (optProblem opt)
        hClose h
        f fname

ubcsat' :: Options -> FilePath -> Maybe FilePath -> IO [(Integer, SAT.Model)]
ubcsat' opt fname varInitFile = do
  let wcnf = optProblem opt
  let args =
        [ "-w" | ".wcnf" `isSuffixOf` map toLower fname] ++
        [ "-alg", "irots"
        , "-seed", "0"
        , "-runs", "10"
        , "-cutoff", show (MaxSAT.numVars wcnf * 50)
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
      return $ scanSolutions (MaxSAT.numVars wcnf) s

scanSolutions :: Int -> String -> [(Integer, SAT.Model)]
scanSolutions nv s = rights $ map (parse (solution nv) "") $ lines s

solution :: Int -> Parser (Integer, SAT.Model)
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
