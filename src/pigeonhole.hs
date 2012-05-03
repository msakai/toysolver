module Main where

import Data.List
import System.Environment
import System.Exit
import System.IO
import PBFile

pigeonHole :: Integer -> Integer -> Formula
pigeonHole p h = (Nothing, cs1 ++ cs2)
  where
    vs :: [((Integer,Integer), Int)]
    vs = zip [(i,j) | i<-[1..p], j<-[1..h]] [1..]

    cs1 :: [Constraint]
    cs1 = [ ([(1,[v]) | j<-[1..h], let Just v = lookup (i,j) vs], PBFile.Ge, 1)
          | i<-[1..p]
          ]
    cs2 :: [Constraint]
    cs2 = [ ([(-1,[v]) | i<-[1..p], let Just v = lookup (i,j) vs], PBFile.Ge, -1)
          | j<-[1..h]
          ]

main :: IO ()
main = do
  xs <- getArgs
  case xs of
    [p,h] -> do
      let opb = pigeonHole (read p) (read h)
      putStr $ showOPB opb ""
    _ -> do
      hPutStrLn stderr "Usage: pigeonhole number_of_pigeons number_of_holes"
      exitFailure
