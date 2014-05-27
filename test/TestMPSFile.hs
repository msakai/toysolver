{-# LANGUAGE TemplateHaskell #-}
module Main (main) where

import Control.Monad
import Data.List
import Data.Maybe
import Test.HUnit hiding (Test)
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import ToySolver.Text.MPSFile

case_testdata = checkString "testdata" testdata
case_example2 = checkFile "samples/mps/example2.mps"
case_ind1     = checkFile "samples/mps/ind1.mps"
case_intvar1  = checkFile "samples/mps/intvar1.mps"
case_intvar2  = checkFile "samples/mps/intvar2.mps"
case_quadobj1 = checkFile "samples/mps/quadobj1.mps"
case_quadobj2 = checkFile "samples/mps/quadobj2.mps"
case_ranges   = checkFile "samples/mps/ranges.mps"
case_sos      = checkFile "samples/mps/sos.mps"
case_sc       = checkFile "samples/mps/sc.mps"

------------------------------------------------------------------------
-- Sample data

testdata :: String
testdata = unlines
  [ "NAME          example2.mps"
  , "ROWS"
  , " N  obj     "
  , " L  c1      "
  , " L  c2      "
  , "COLUMNS"
  , "    x1        obj                 -1   c1                  -1"
  , "    x1        c2                   1"
  , "    x2        obj                 -2   c1                   1"
  , "    x2        c2                  -3"
  , "    x3        obj                 -3   c1                   1"
  , "    x3        c2                   1"
  , "RHS"
  , "    rhs       c1                  20   c2                  30"
  , "BOUNDS"
  , " UP BOUND     x1                  40"
  , "ENDATA"
  ]

------------------------------------------------------------------------
-- Utilities

checkFile :: FilePath -> IO ()
checkFile fname = do
  r <- parseFile fname
  case r of
    Left err -> assertFailure (show err)
    Right lp -> return ()

checkString :: String -> String -> IO ()
checkString name str = do
  case parseString name str of
    Left err -> assertFailure (show err)
    Right lp -> return ()

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
