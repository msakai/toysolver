{-# LANGUAGE CPP #-}
module Main where

import qualified Data.ByteString.Builder as ByteStringBuilder
import Data.List
import qualified Data.Map as Map
import Data.Map (Map)
import System.Environment
import System.Exit
import System.IO
import Data.PseudoBoolean as PBFile
import qualified ToySolver.FileFormat as FF
import ToySolver.Internal.Util (setEncodingChar8)

pigeonHole :: Integer -> Integer -> Formula
pigeonHole p h =
  Formula
  { pbObjectiveFunction = Nothing
  , pbConstraints = cs1 ++ cs2
  , pbNumVars = fromIntegral $ p*h
  , pbNumConstraints = fromIntegral $ p+h
  }
  where
    vs :: Map (Integer,Integer) Int
    vs = Map.fromList $ zip [(i,j) | i<-[1..p], j<-[1..h]] [1..]

    cs1 :: [Constraint]
    cs1 = [ ([(1,[v]) | j<-[1..h], let v = vs Map.! (i,j)], PBFile.Ge, 1)
          | i<-[1..p]
          ]
    cs2 :: [Constraint]
    cs2 = [ ([(-1,[v]) | i<-[1..p], let v = vs Map.! (i,j)], PBFile.Ge, -1)
          | j<-[1..h]
          ]

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif

  xs <- getArgs
  case xs of
    [p,h] -> do
      let opb = pigeonHole (read p) (read h)
      ByteStringBuilder.hPutBuilder stdout $ FF.render opb
    _ -> do
      hPutStrLn stderr "Usage: pigeonhole number_of_pigeons number_of_holes"
      exitFailure
