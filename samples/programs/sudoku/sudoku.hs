{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
module Main where

import Control.Monad
import Data.Array.IArray
import Data.Char
import System.Environment
import System.Exit
import System.IO
import qualified ToySolver.SAT as SAT

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fname] -> do
      s <- readFile fname
      let b = readBoard $ filter (not . isSpace) $ removeComments s
      ans <- solve b
      case ans of
        Nothing -> hPutStrLn stderr "NO SOLUTION"
        Just b2 -> do
          hPutStrLn stderr "SOLUTION FOUND"
          printAnswer b2
    _ -> do
      hPutStrLn stderr "Usage: sudoku input.sdk"
      exitFailure

removeComments :: String -> String
removeComments = unlines . filter p . lines
  where
    p ('#':_) = False
    p _ = True

readBoard :: String -> Array (Int,Int) (Maybe Int)
readBoard s = array ((1,1),(9,9)) $ 
  [ (idx, if isDigit c then Just (read [c]) else Nothing)
  | (idx, c) <- zip [(i,j) | i <- [1..9], j <- [1..9]] s
  ]

solve :: Array (Int,Int) (Maybe Int) -> IO (Maybe (Array (Int,Int) Int))
solve board = do
  solver <- SAT.newSolver 
  SAT.setLogger solver (hPutStrLn stderr)
 
  (vs :: Array (Int,Int,Int) SAT.Var) <-
    liftM (array ((1,1,1), (9,9,9))) $
      forM [(i,j,k) | i<-[1..9], j<-[1..9], k<-[1..9]] $ \idx -> do
        v <- SAT.newVar solver
        return (idx,v)

  forM_ (assocs board) $ \((i,j), m) -> do
    case m of 
      Nothing -> return ()
      Just k -> SAT.addClause solver [vs ! (i,j,k)]

  -- Every cell contains exactly one digit.
  forM_ [1..9] $ \i -> do
    forM_ [1..9] $ \j -> do
      SAT.addExactly solver [vs ! (i,j,k) | k <- [1..9]] 1

  forM_ [1..9] $ \k -> do
    -- Every row contains exactly one occurence of the digit.
    forM_ [1..9] $ \i -> do
      SAT.addExactly solver [vs ! (i,j,k) | j <- [1..9]] 1
    -- Every column contains exactly one occurence of the digit.
    forM_ [1..9] $ \j -> do
      SAT.addExactly solver [vs ! (i,j,k) | i <- [1..9]] 1
    -- Every block contains exactly one occurence of the digit.
    forM_ [0..2] $ \bi ->
      forM_ [0..2] $ \bj ->
        SAT.addExactly solver [vs ! (bi*3 + i', bj*3 + j', k) | i' <- [1..3], j' <- [1..3]] 1

  ret <- SAT.solve solver
  if ret then do
    m <- SAT.getModel solver
    return $ Just $ array ((1,1),(9,9)) [((i,j),k) | ((i,j,k),v) <- assocs vs, m ! v]
  else
    return Nothing

printAnswer :: Array (Int,Int) Int -> IO ()
printAnswer b =
  forM_ [1..9] $ \i ->
    putStrLn $ concat [show (b ! (i,j)) | j <- [1..9]]
