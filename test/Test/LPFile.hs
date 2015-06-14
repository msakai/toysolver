{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Test.LPFile (lpTestGroup) where

import Control.Monad
import Data.Default.Class
import Data.List
import Data.Maybe
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified ToySolver.Data.MIP as MIP
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

checkFile :: FilePath -> Assertion
checkFile fname = do
  r <- parseFile def fname
  case r of
    Left err -> assertFailure $ show err
    Right (lp :: MIP.Problem String Rational) ->
      case render def lp of
        Left err -> assertFailure ("render failure: " ++ err)
        Right _ -> return ()

checkString :: String -> String -> Assertion
checkString name str = do
  case parseString def name str of
    Left err -> assertFailure $ show err
    Right (lp :: MIP.Problem String Rational) ->
      case render def lp of
        Left err -> assertFailure ("render failure: " ++ err)
        Right _ -> return ()

------------------------------------------------------------------------
-- Test harness

lpTestGroup :: TestTree
lpTestGroup = $(testGroupGenerator)
