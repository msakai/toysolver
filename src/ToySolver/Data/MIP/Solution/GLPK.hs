{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
module ToySolver.Data.MIP.Solution.GLPK
  ( Solution (..)
  , parse
  , readFile
  ) where

import Prelude hiding (readFile, writeFile)
import Control.Applicative
import Data.Interned (intern)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Scientific (Scientific)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TLIO
import ToySolver.Data.MIP (Solution)
import qualified ToySolver.Data.MIP as MIP

parse :: TL.Text -> MIP.Solution Scientific
parse t = parse' $ TL.lines t

parse' :: [TL.Text] -> MIP.Solution Scientific
parse' ls =
  case parseHeaders ls of
    (headers, ls2) ->
      case parseColumns (skipRows ls2) of
        (vs, _) ->
          let status = Map.findWithDefault MIP.StatusUnknown (headers Map.! "Status") statusTable
              objstr = headers Map.! "Objective"
              objstr2 = 
                case T.findIndex ('='==) objstr of
                  Nothing -> objstr
                  Just idx -> T.drop (idx+1) objstr
              obj = case reads (T.unpack objstr2) of
                      [] -> error "parse error"
                      (r,_):_ -> r
          in MIP.Solution
             { MIP.solStatus = status
             , MIP.solObjectiveValue = Just obj
             , MIP.solVariables = vs
             }

parseHeaders :: [TL.Text] -> (Map T.Text T.Text, [TL.Text])
parseHeaders = f Map.empty
  where
    f _ [] = error "parse error"
    f ret ("":ls) = (ret, ls)
    f ret (l:ls) =
      case TL.break (':'==) l of
        (_, "") -> error "parse error"
        (name, val) -> f (Map.insert (TL.toStrict name) (TL.toStrict (TL.strip (TL.tail val))) ret) ls

skipRows :: [TL.Text] -> [TL.Text]
skipRows [] = error "parse error"
skipRows ("":ls) = ls
skipRows (_:ls) = skipRows ls

parseColumns :: [TL.Text] -> (Map MIP.Var Scientific, [TL.Text])
parseColumns (l1:l2:ls)
  | l1 == "   No. Column name       Activity     Lower bound   Upper bound"
  , l2 == "------ ------------    ------------- ------------- -------------"
    = f [] ls
  where
    f :: [(MIP.Var, Scientific)] -> [TL.Text] -> (Map MIP.Var Scientific, [TL.Text])
    f _ [] = error "parse error"
    f ret ("":ls2) = (Map.fromList ret, ls2)
    f ret (l:ls2) =
      case ws of
        (_no : col : "*" : activity : _) -> f ((intern (TL.toStrict col), read (TL.unpack activity)) : ret) ls3
        (_no : col : activity : _) -> f ((intern (TL.toStrict col), read (TL.unpack activity)) : ret) ls3
        _ -> error "parse error"
      where
        (ws,ls3) =
          case TL.words l of
            ws1@(_:_:_:_) -> (ws1, ls2)
            ws1@[_,_] -> (ws1 ++ TL.words (head ls2), tail ls2)
            _ -> error "parse error"
parseColumns _ = error "parse error"

statusTable :: Map T.Text MIP.Status
statusTable = Map.fromList
  [ ("INTEGER OPTIMAL", MIP.StatusOptimal)
  , ("INTEGER NON-OPTIMAL", MIP.StatusUnknown)
  , ("INTEGER EMPTY", MIP.StatusInfeasible)
  ]

readFile :: FilePath -> IO (MIP.Solution Scientific)
readFile fname = parse <$> TLIO.readFile fname
