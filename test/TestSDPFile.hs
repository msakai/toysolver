{-# LANGUAGE TemplateHaskell #-}
module TestSDPFile (sdpTestGroup) where

import Control.Monad
import Data.List
import Data.Maybe
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH
import ToySolver.Text.SDPFile

------------------------------------------------------------------------
-- Sample data

example1 :: Problem
example1
  = Problem
  { blockStruct = [2]
  , costs       = [48, -8, 20]
  , matrices    = map denseMatrix [f0,f1,f2,f3]
  }
  where
    f0 = [[[-11,0], [0,23]]]
    f1 = [[[10,4],  [4,0]]]
    f2 = [[[0,0],  [0,-8]]]
    f3 = [[[0,-8], [-8,-2]]]

example2 :: Problem
example2
  = Problem
  { blockStruct = [2,3,-2]
  , costs       = [1.1, -10, 6.6, 19, 4.1]
  , matrices    = map denseMatrix [f0,f1,f5]
  }
  where
    f0 = [ [[-1.4, -3.2], [-3.2, -28]]
         , [[15, -12, 2.1], [-12, 16, -3.8], [2.1, -3.8, 15]] 
         , [[1.8, 0], [0, -4.0]] 
         ]
    f1 = [ [[0.5, 5.2], [5.2,-5.3]]
         , [[7.8, -2.4, 6.0], [-2.4, 4.2, 6.5], [6.0, 6.5, 2.1]] 
         , [[-4.5, 0], [0, -3.5]]
         ]
    f5 = [ [[-6.5, -5.4], [-5.4, -6.6]]
         , [[6.7, -7.2, -3.6], [-7.2, 7.3, -3.0], [-3.6, -3.0, -1.4]] 
         , [[6.1, 0],[0, -1.5]] 
         ]

case_test1 = checkParsed example1b example1
  where
    s = render example1 ""
    example1b = parseDataString "" s

case_test2 = checkParsed example1b example1
  where
    s = renderSparse example1 ""
    example1b = parseSparseDataString "" s

case_test3 = checkParsed example2b example2
  where
    s = render example2 ""
    example2b = parseDataString "" s

case_test4 = checkParsed example2b example2
  where
    s = renderSparse example2 ""
    example2b = parseSparseDataString "" s

-- checkParsed :: Either ParseError Problem -> Problem -> IO ()
checkParsed actual expected =
  case actual of
    Left err -> assertFailure $ show err
    Right prob -> prob @?= expected

------------------------------------------------------------------------
-- Test harness

sdpTestGroup :: TestTree
sdpTestGroup = $(testGroupGenerator)
