{-# LANGUAGE TemplateHaskell #-}
module Main (main) where

import Control.Monad
import Data.List
import Data.Maybe
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH
import ToySolver.Data.MIP.LPFile

case_testdata       = checkString "testdata" testdata
case_test_indicator = checkFile "samples/lp/test-indicator.lp"
case_test_qcp       = checkFile "samples/lp/test-qcp.lp"
case_test_qcp2      = checkFile "samples/lp/test-qcp2.lp"
case_test_qp        = checkFile "samples/lp/test-qp.lp"
case_empty_obj_1    = checkFile "samples/lp/empty_obj_1.lp"
case_empty_obj_2    = checkFile "samples/lp/empty_obj_2.lp"  

------------------------------------------------------------------------
-- Sample data

testdata :: String
testdata = unlines
  [ "Maximize"
  , " obj: x1 + 2 x2 + 3 x3 + x4"
  , "Subject To"
  , " c1: - x1 + x2 + x3 + 10 x4 <= 20"
  , " c2: x1 - 3 x2 + x3 <= 30"
  , " c3: x2 - 3.5 x4 = 0"
  , "Bounds"
  , " 0 <= x1 <= 40"
  , " 2 <= x4 <= 3"
  , "General"
  , " x4"
  , "End"
  ]

------------------------------------------------------------------------
-- Utilities

checkFile :: FilePath -> IO ()
checkFile fname = do
  r <- parseFile fname
  case r of
    Left err -> assertFailure $ show err
    Right lp ->
      case render lp of
        Left err -> assertFailure ("render failure: " ++ err)
        Right _ -> return ()

checkString :: String -> String -> IO ()
checkString name str = do
  case parseString name str of
    Left err -> assertFailure $ show err
    Right lp ->
      case render lp of
        Left err -> assertFailure ("render failure: " ++ err)
        Right _ -> return ()

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
