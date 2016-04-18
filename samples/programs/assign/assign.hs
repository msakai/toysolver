{-
A program for solving following assignment problems from
<http://people.brunel.ac.uk/~mastjjb/jeb/orlib/assigninfo.html>.

Problem set        Files
100                assign100
200                assign200
300                assign300
400                assign400
500                assign500
600                assign600
700                assign700
800                assign800

Use "-p" option to solve those problem.

Problem set        Files
800                assignp800
1500               assignp1500
3000               assignp3000
5000               assignp5000
-}
module Main where

import Control.Applicative
import Control.Monad
import Data.Attoparsec.ByteString.Char8 hiding (isSpace)
import qualified Data.Attoparsec.ByteString.Lazy as AL
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.Char
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.List
import qualified Data.Vector.Unboxed as VU
import System.Environment
import ToySolver.Combinatorial.WeightedBipartiteMatching

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fname] -> do
      s <- BL.readFile fname
      let (as, bs, w) = parse1 s
          (obj, m, _) = minimumPerfectMatching as bs w
      putStrLn $ "obj = " ++ show obj
      forM_ (HashSet.toList m) $ \(a,b) -> do
        putStrLn $ unwords $ map show [a,b]
    ["-pp", fname] -> do
      s <- BL.readFile fname
      let (as, bs, w) = parse1 s
          es = [(a, b, w a b) | a <- HashSet.toList as, b <- HashSet.toList bs]
      case minimumPerfectMatching' as bs es of
        Nothing ->
          putStrLn $ "infeasible"
        Just (obj, m, _) -> do
          putStrLn $ "obj = " ++ show obj
          forM_ (HashSet.toList m) $ \(a,b) -> do
            putStrLn $ unwords $ map show [a,b]
    ["-p", fname] -> do
      s <- BL.readFile fname
      let (as, bs, es) = parse2 s
      case minimumPerfectMatching' as bs es of
        Nothing ->
          putStrLn $ "infeasible"
        Just (obj, m, _) -> do
          putStrLn $ "obj = " ++ show obj
          forM_ (HashSet.toList m) $ \(a,b) -> do
            putStrLn $ unwords $ map show [a,b]

parse1 :: BL.ByteString -> (HashSet Int, HashSet Int, Int -> Int -> Int)
parse1 s = (as, bs, w)
  where
    f s =
      case BL.readInt s of
        Nothing -> Nothing
        Just (i,s') -> Just (i, BL.dropWhile isSpace s')
    (n:xs) = unfoldr f (BL.dropWhile isSpace s)
    tbl :: VU.Vector Int
    tbl = VU.fromListN (n*n) xs
    as = HashSet.fromList [0..n-1]
    bs = as
    w a b = tbl VU.! (a*n+b)

parse2 :: BL.ByteString -> (HashSet Int, HashSet Int, [(Int,Int,Int)])
parse2 s =
  case AL.eitherResult (AL.parse pfile s) of
    Left s -> error s
    Right x -> x

pfile :: Parser (HashSet Int, HashSet Int, [(Int,Int,Int)])
pfile = do
  skipSpace
  n <- decimal <* skipSpace
  let p es =
        mplus
          (do a <- decimal <* skipSpace
              b <- decimal <* skipSpace
              w <- decimal <* skipSpace
              p ((a,b,w) : es))
          (endOfInput *> return es)
  es <- p []
  let as = HashSet.fromList [1..n]
      bs = as
  return (as, bs, es)
