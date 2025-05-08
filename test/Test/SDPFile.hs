{-# LANGUAGE TemplateHaskell #-}
module Test.SDPFile (sdpTestGroup) where

import Control.Monad
import qualified Data.Aeson as J
import Data.Maybe
import Data.ByteString.Builder (toLazyByteString)
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH

import qualified ToySolver.SDP as SDP
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
    s = toLazyByteString $ renderData example1
    example1b = parseData "" s

case_test2 = checkParsed example1b example1
  where
    s = toLazyByteString $ renderSparseData example1
    example1b = parseSparseData "" s

case_test3 = checkParsed example2b example2
  where
    s = toLazyByteString $ renderData example2
    example2b = parseData "" s

case_test4 = checkParsed example2b example2
  where
    s = toLazyByteString $ renderSparseData example2
    example2b = parseSparseData "" s

-- checkParsed :: Either ParseError Problem -> Problem -> Assertion
checkParsed actual expected =
  case actual of
    Left err -> assertFailure $ show err
    Right prob -> prob @?= expected

------------------------------------------------------------------------

case_dualize_json_example1 :: Assertion
case_dualize_json_example1 = do
  let ret@(_, info) = SDP.dualize example1
      json = J.encode info
  J.eitherDecode json @?= Right info

case_dualize_json_example2 :: Assertion
case_dualize_json_example2 = do
  let ret@(_, info) = SDP.dualize example2
      json = J.encode info
  J.eitherDecode json @?= Right info

------------------------------------------------------------------------
-- Test harness

sdpTestGroup :: TestTree
sdpTestGroup = $(testGroupGenerator)
