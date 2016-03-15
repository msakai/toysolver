{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
module UBCSAT
  ( ubcsat
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
import Text.ParserCombinators.Parsec hiding (try)

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

ubcsat :: Options -> IO (Maybe SAT.Model)
ubcsat opt = do
  dir <- case optTempDir opt of
           Just dir -> return dir
           Nothing -> getTemporaryDirectory

  let f fname
        | null (optVarInit opt) = ubcsat' opt fname Nothing
        | otherwise = do
            withTempFile dir ".txt" $ \varInitFile h -> do
              hSetBinaryMode h True
              hSetBuffering h (BlockBuffering Nothing)
              hPutStrLn h $ intercalate " "  (map show (optVarInit opt))
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

ubcsat' :: Options -> FilePath -> Maybe FilePath -> IO (Maybe SAT.Model)
ubcsat' opt fname varInitFile = do
  let wcnf = optProblem opt
  let args =
        [ "-w" | ".wcnf" `isSuffixOf` map toLower fname] ++
        [ "-alg", "irots"
        , "-seed", "0"
        , "-runs", "10"
        , "-cutoff", show (MaxSAT.numVars wcnf * 50)
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
      return Nothing
    Right s -> do
      forM_ (lines s) $ \l -> putStr "c " >> putStrLn l
      case scanSolutions s of
        [] -> return Nothing
        sols -> do
          let (obj,m) = minimumBy (compare `on` fst) sols
          if obj < MaxSAT.topCost wcnf then
            return $ Just $ array (1, MaxSAT.numVars wcnf) (zip [1..] m)
          else
            return Nothing

scanSolutions :: String -> [(Integer, [Bool])]
scanSolutions s = rights $ map (parse solution "") $ lines s

solution :: Parser (Integer, [Bool])
solution = do
  skipMany1 digit
  spaces
  _ <- char '0' <|> char '1'
  spaces
  obj <- liftM read $ many1 digit
  spaces
  values <- many ((char '0' >> return False) <|> (char '1' >> return True))
  return (obj, values)
