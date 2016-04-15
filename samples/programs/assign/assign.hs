{-
A program for solving following assignment problems from
<http://people.brunel.ac.uk/~mastjjb/jeb/orlib/assigninfo.html>.

Problem set        Files
800                assignp800
1500               assignp1500
3000               assignp3000
5000               assignp5000
-}
module Main where

import Control.Monad
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.Char
import qualified Data.HashSet as HashSet
import Data.List
import qualified Data.Vector.Unboxed as VU
import System.Environment
import ToySolver.Combinatorial.WeightedBipartiteMatching

main :: IO ()
main = do
  [fname] <- getArgs
  s <- BL.readFile fname
  let f s =
        case BL.readInt s of
          Nothing -> Nothing
          Just (i,s') -> Just (i, BL.dropWhile isSpace s')
      (n:xs) = unfoldr f (BL.dropWhile isSpace s)
      tbl :: VU.Vector Int
      tbl = VU.fromListN (n*n) xs
      as = HashSet.fromList [0..n-1]
      bs = as
      w a b = tbl VU.! (a*n+b)
      (obj, m, _) = minimumPerfectMatching as bs w
  putStrLn $ "obj = " ++ show obj
  forM_ (HashSet.toList m) $ \(a,b) -> do
    putStrLn $ unwords $ map show [a,b]
