{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
module UBCSAT (ubcsat) where

import Control.Exception
import Control.Monad
import Data.Array.IArray
import Data.Char
import Data.Either
import Data.Function
import Data.List
import System.Process
import Text.ParserCombinators.Parsec hiding (try)

import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.Text.MaxSAT as MaxSAT

ubcsat :: FilePath -> FilePath -> MaxSAT.WCNF -> IO (Maybe SAT.Model)
ubcsat cmd fname wcnf = do
  let args =
        [ "-w" | ".wcnf" `isSuffixOf` map toLower fname] ++
        [ "-alg", "irots"
        , "-seed", "0"
        , "-runs", "10"
        , "-cutoff", show (MaxSAT.numVars wcnf * 50)
        , "-solve"
        , "-r", "bestsol"
        , "-inst", fname
        ]
      stdinStr = ""
    
  ret <- try $ readProcess cmd args stdinStr
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
