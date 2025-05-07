{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Control.Exception
import Control.Monad
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.Char
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import Data.Int
import Data.List (sortBy)
import Data.Maybe
import Data.Ord
import qualified Data.Sequence as Seq
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
import qualified ToySolver.Graph.ShortestPath as ShortestPath
import ToySolver.Internal.Util (setEncodingChar8)

data Flag
  = Help
  | PrintResult
  | Method String
  deriving Eq

options :: [OptDescr Flag]
options =
    [ Option ['h'] ["help"] (NoArg Help) "show help"
    , Option []    ["print"]  (NoArg PrintResult)  "print result"
    , Option []    ["method"] (ReqArg Method "STRING") "method: dijkstra, bellman-ford, floyd-warshall"
    ]

header :: String
header = unlines
  [ "Usage:"
  , "    shortest-path [OPTIONS] INPUTFILE VERTEX.."
  , ""
  , "Options:"
  ]

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif
  args <- getArgs
  case getOpt Permute options args of
    (o,_,[])
      | Help `elem` o -> putStrLn (usageInfo header options)
    (o,fname:vs',[]) -> do
      let method = last ("dijkstra" : [m | Method m <- o])
          vs0 = map read vs'
          vs = if null vs0 then [1] else vs0
      es <- load fname
      let g :: ShortestPath.Graph Int64 Int
          g = fmap toList $ IntMap.fromListWith (<>) [(s, Seq.singleton (t,fromIntegral w,i)) | (i,(s,t,w)) <- zip [(1::Int)..] es]
      case filter (\c -> c /= '-' && c /= '_') (map toLower method) of
        "dijkstra" -> do
          let ret = ShortestPath.dijkstra ShortestPath.unit g vs
          _ <- evaluate ret
          when (PrintResult `elem` o) $ do
            forM_ (sortBy (comparing fst) (IntMap.toList ret)) $ \(v, (cost,_)) -> do
              putStrLn $ show v ++ ": " ++ show cost
        "bellmanford" -> do
          let ret = ShortestPath.bellmanFord ShortestPath.unit g vs
          _ <- evaluate ret
          when (PrintResult `elem` o) $ do
            forM_ (sortBy (comparing fst) (IntMap.toList ret)) $ \(v, (cost,_)) -> do
              putStrLn $ show v ++ ": " ++ show cost
        "floydwarshall" -> do
          let ret = ShortestPath.floydWarshall ShortestPath.unit g
          _ <- evaluate ret
          when (PrintResult `elem` o) $ do
            forM_ (sortBy (comparing fst) (IntMap.toList ret)) $ \(v, m) -> do
              forM_ (sortBy (comparing fst) (IntMap.toList m)) $ \(u, (cost,_)) -> do
                putStrLn $ show v ++ "-" ++ show u ++ ": " ++ show cost
        _ -> error ("unknown method: " ++ method)
    (_,_,errs) -> do
      hPutStrLn stderr $ concat errs ++ usageInfo header options
      exitFailure

load :: FilePath -> IO [(Int,Int,Int)]
load fname = do
  s <- BL.readFile fname
  let f l = do
        -- 'BL.stripPrefix' is available only on bytestring >=0.10.8.0,
        -- But we still want to support bytestring-0.10.4.0 (lts-2.22) and bytestring-0.10.6.0 (lts-3.22).
        (c,l2) <- BL.uncons l
        guard $ c == 'a'
        (v,l3) <- BL.readInt $ BL.dropWhile isSpace l2
        (u,l4) <- BL.readInt $ BL.dropWhile isSpace l3
        (w,_)  <- BL.readInt $ BL.dropWhile isSpace l4
        return (v,u,w)
  return $ catMaybes [f l | l <- BL.lines s]
