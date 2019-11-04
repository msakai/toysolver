{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
module Main where

import Control.Monad
import Data.Array.IArray
import System.Environment
import qualified ToySolver.SAT as SAT
import ToySolver.Internal.Util (setEncodingChar8)

main :: IO ()
main = do
#ifdef FORCE_CHAR8
  setEncodingChar8
#endif

  [s] <- getArgs
  let n = read s
  ans <- solve n
  case ans of
    Nothing -> putStrLn "NO SOLUTION"
    Just m -> do
      forM_ [1..n] $ \i -> do
        putStrLn [if m ! (i,j) then 'Q' else '.' | j <- [1..n]]

solve :: Int -> IO (Maybe (Array (Int,Int) Bool))
solve n = do
  solver <- SAT.newSolver
  (a :: Array (Int,Int) SAT.Var)  <- liftM (array ((1,1),(n,n))) $ forM [(i,j) | i <- [1..n], j <- [1..n]] $ \(i,j) -> do
    x <- SAT.newVar solver
    return ((i,j),x)

  forM_ [1..n] $ \i -> do
    SAT.addExactly solver [a ! (i,j) | j <- [1..n]] 1
  forM_ [1..n] $ \j -> do
    SAT.addExactly solver [a ! (i,j) | i <- [1..n]] 1

  forM_ [1..n] $ \k -> do
    SAT.addAtMost solver [a ! (k+o,1+o) | o <- [0..(n-k)]] 1
  forM_ [2..n] $ \k -> do
    SAT.addAtMost solver [a ! (1+o,k+o) | o <- [0..(n-k)]] 1

  forM_ [1..n] $ \k -> do
    SAT.addAtMost solver [a ! (k-o,1+o) | o <- [0 .. k-1]] 1
  forM_ [2..n] $ \k -> do
    SAT.addAtMost solver [a ! (k+o,n-o) | o <- [0..(n-k)]] 1

  ret <- SAT.solve solver
  if ret then do
    m <- SAT.getModel solver
    return $ Just $ fmap (SAT.evalLit m) a
  else
    return Nothing
