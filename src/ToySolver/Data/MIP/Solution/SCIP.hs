{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
module ToySolver.Data.MIP.Solution.SCIP
  ( Solution (..)
  , parse
  , readFile
  ) where

import Prelude hiding (readFile, writeFile)
import Control.Applicative
import Control.Monad.Except
import Data.Interned (intern)
import qualified Data.Map as Map
import Data.Scientific (Scientific)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TLIO
import ToySolver.Data.MIP (Solution)
import qualified ToySolver.Data.MIP as MIP

parse :: TL.Text -> (T.Text, MIP.Solution Scientific)
parse t =
  case parse' $ TL.lines t of
    Left e -> error e
    Right x -> x

parse' :: [TL.Text] -> Either String (T.Text, MIP.Solution Scientific)
parse' (t1:t2:ts) = do
  status <-
    case TL.stripPrefix "solution status:" t1 of
      Nothing -> throwError "first line must start with \"solution status:\""
      Just s -> return $ TL.toStrict $ TL.strip s
  obj <-
    case TL.stripPrefix "objective value:" t2 of
      Nothing -> throwError "second line must start with \"objective value:\""
      Just s -> return $ read $ TL.unpack $ TL.strip s
  let f :: [(MIP.Var, Scientific)] -> TL.Text -> Either String [(MIP.Var, Scientific)]
      f vs t =
        case TL.words t of
          (w1:w2:_) -> return $ (intern (TL.toStrict w1), read (TL.unpack w2)) : vs
          [] -> return $ vs
          _ -> throwError ("ToySolver.Data.MIP.Solution.SCIP: invalid line " ++ show t)
  vs <- foldM f [] ts
  return $ (status, MIP.Solution{ MIP.solObjectiveValue = Just obj, MIP.solVariables = Map.fromList vs })
parse' _ = throwError "must have >=2 lines"

readFile :: FilePath -> IO (T.Text, MIP.Solution Scientific)
readFile fname = parse <$> TLIO.readFile fname
