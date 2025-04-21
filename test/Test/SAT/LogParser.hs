{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.SAT.LogParser (satLogParserTestGroup) where

import Data.Array.IArray
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import ToySolver.SAT.LogParser


case_parseSATLog :: Assertion
case_parseSATLog = parseSATLog input @?= expected
  where
    input = unlines
      [ "c foo"
      , "s SATISFIABLE"
      , "c bar"
      , "v -1 -2 3 4 -5"
      , "c baz"
      , "v 6 -7 8 9 -10"
      , "c quz"
      , "v 0"
      ]
    expected = array (1, 10) [(1, False), (2, False), (3, True), (4, True), (5, False), (6, True), (7, False), (8, True), (9, True), (10, False)]

case_parseMaxSatLog_old :: Assertion
case_parseMaxSatLog_old = parseMaxSATLog input @?= expected
  where
    input = unlines
      [ "c foo"
      , "o 4750"
      , "o 232"
      , "s OPTIMUM FOUND"
      , "c bar"
      , "v -1 -2 3 4 -5"
      , "c baz"
      , "v 6 -7 8 9 -10"
      , "c quz"
      ]
    expected = array (1, 10) [(1, False), (2, False), (3, True), (4, True), (5, False), (6, True), (7, False), (8, True), (9, True), (10, False)]

case_parseMaxSatLog_new :: Assertion
case_parseMaxSatLog_new = parseMaxSATLog input @?= expected
  where
    input = unlines
      [ "c foo"
      , "o 4750"
      , "o 232"
      , "s OPTIMUM FOUND"
      , "c bar"
      , "v 00110"
      , "c baz"
      , "v 10110"
      , "c quz"
      ]
    expected = array (1, 10) [(1, False), (2, False), (3, True), (4, True), (5, False), (6, True), (7, False), (8, True), (9, True), (10, False)]

case_parsePBLog :: Assertion
case_parsePBLog = parsePBLog input @?= expected
  where
    input = unlines
      [ "c foo"
      , "o 4750"
      , "o 232"
      , "s OPTIMUM FOUND"
      , "c bar"
      , "v -x1 -x2 x3 x4 -x5"
      , "c baz"
      , "v x6 -x7 x8 x9 -x10"
      , "c quz"
      ]
    expected = array (1, 10) [(1, False), (2, False), (3, True), (4, True), (5, False), (6, True), (7, False), (8, True), (9, True), (10, False)]

satLogParserTestGroup :: TestTree
satLogParserTestGroup = $(testGroupGenerator)
