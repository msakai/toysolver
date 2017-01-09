{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
module ToySolver.Data.MIP.Solution.CBC
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
parse' (l1:ls) = do
  (status, obj) <-
    case TL.break ('-'==) l1 of
      (s1,s2) -> 
        case TL.stripPrefix "- objective value " s2 of
          Nothing -> throwError "fail to parse header"
          Just s3 -> return (TL.toStrict (TL.strip s1), read (TL.unpack s3))
  let f :: [(MIP.Var, Scientific)] -> TL.Text -> Either String [(MIP.Var, Scientific)]
      f vs t =
        case TL.words t of
          ("**":_no:var:val:_) -> return $ (intern (TL.toStrict var), read (TL.unpack val)) : vs
          (_no:var:val:_) -> return $ (intern (TL.toStrict var), read (TL.unpack val)) : vs
          [] -> return $ vs
          _ -> throwError ("ToySolver.Data.MIP.Solution.CBC: invalid line " ++ show t)
  vs <- foldM f [] ls
  return $ (status, MIP.Solution{ MIP.solObjectiveValue = Just obj, MIP.solVariables = Map.fromList vs })
parse' _ = throwError "must have >=1 lines"

readFile :: FilePath -> IO (T.Text, MIP.Solution Scientific)
readFile fname = parse <$> TLIO.readFile fname
