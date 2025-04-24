{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.SAT.LogParser (satLogParserTestGroup) where

import Data.Array.IArray
import qualified Data.ByteString.Lazy.Char8 as BL
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import ToySolver.SAT.LogParser

-- ------------------------------------------------------------------------

case_parseSATLog_SATISFIABLE :: Assertion
case_parseSATLog_SATISFIABLE = parseSATLog input @?= expected
  where
    input = BL.unlines
      [ "c foo"
      , "s SATISFIABLE"
      , "c bar"
      , "v -1 -2 3 4 -5"
      , "c baz"
      , "v 6 -7 8 9 -10"
      , "c quz"
      , "v 0"
      ]
    expected =
      ( "SATISFIABLE"
      , Just $ array (1, 10) [(1, False), (2, False), (3, True), (4, True), (5, False), (6, True), (7, False), (8, True), (9, True), (10, False)]
      )

case_parseSATLog_UNSATISFIABLE :: Assertion
case_parseSATLog_UNSATISFIABLE = parseSATLog input @?= expected
  where
    input = BL.unlines
      [ "c foo"
      , "s UNSATISFIABLE"
      , "c bar"
      ]
    expected =
      ( "UNSATISFIABLE"
      , Nothing
      )

case_parseSATLog_UNKNOWN :: Assertion
case_parseSATLog_UNKNOWN = parseSATLog input @?= expected
  where
    input = BL.unlines
      [ "c foo"
      , "s UNKNOWN"
      , "c bar"
      ]
    expected =
      ( "UNKNOWN"
      , Nothing
      )

case_parseSATLog_UNKNOWN_implicit :: Assertion
case_parseSATLog_UNKNOWN_implicit = parseSATLog input @?= expected
  where
    input = BL.unlines ["c foo"]
    expected =
      ( "UNKNOWN"
      , Nothing
      )

-- ------------------------------------------------------------------------

case_parseMaxSATLog_UNSATISFIABLE :: Assertion
case_parseMaxSATLog_UNSATISFIABLE = parseMaxSATLog input @?= expected
  where
    input = BL.unlines
      [ "c foo"
      , "s UNSATISFIABLE"
      , "c bar"
      ]
    expected =
      ( "UNSATISFIABLE"
      , Nothing
      , Nothing
      )

case_parseMaxSATLog_UNKNOWN :: Assertion
case_parseMaxSATLog_UNKNOWN = parseMaxSATLog input @?= expected
  where
    input = BL.unlines
      [ "c foo"
      , "s UNKNOWN"
      , "c bar"
      ]
    expected =
      ( "UNKNOWN"
      , Nothing
      , Nothing
      )

case_parseMaxSATLog_UNKNOWN_implicit :: Assertion
case_parseMaxSATLog_UNKNOWN_implicit = parsePBLog input @?= expected
  where
    input = BL.unlines ["c foo"]
    expected =
      ( "UNKNOWN"
      , Nothing
      , Nothing
      )

case_parseMaxSATLog_OPTIMUM_FOUND_old :: Assertion
case_parseMaxSATLog_OPTIMUM_FOUND_old = parseMaxSATLog input @?= expected
  where
    input = BL.unlines
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
    expected =
      ( "OPTIMUM FOUND"
      , Just 232
      , Just $ array (1, 10) [(1, False), (2, False), (3, True), (4, True), (5, False), (6, True), (7, False), (8, True), (9, True), (10, False)]
      )

case_parseMaxSATLog_OPTIMUM_FOUND_new :: Assertion
case_parseMaxSATLog_OPTIMUM_FOUND_new = parseMaxSATLog input @?= expected
  where
    input = BL.unlines
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
    expected =
      ( "OPTIMUM FOUND"
      , Just 232
      , Just $ array (1, 10) [(1, False), (2, False), (3, True), (4, True), (5, False), (6, True), (7, False), (8, True), (9, True), (10, False)]
      )

-- Special Track on Incomplete Solvers allowed multiple v-lines
-- http://maxsat.ia.udl.cat/requirements/
case_parseMaxSATLog_multiple_vlines :: Assertion
case_parseMaxSATLog_multiple_vlines = parseMaxSATLog input @?= expected
  where
    input = BL.unlines
      [ "c foo"
      , "o 4750"
      , "v 1 2 3 4 5 6 7 8 9 10"
      , "o 232"
      , "c bar"
      , "v -1 -2 3 4 -5 6 -7 8 9 -10"
      , "s SATISFIABLE"
      , "c quz"
      ]
    expected =
      ( "SATISFIABLE"
      , Just 232
      , Just $ array (1, 10) [(1, False), (2, False), (3, True), (4, True), (5, False), (6, True), (7, False), (8, True), (9, True), (10, False)]
      )

-- ------------------------------------------------------------------------

case_parsePBLog_OPTIMUM_FOUND :: Assertion
case_parsePBLog_OPTIMUM_FOUND = parsePBLog input @?= expected
  where
    input = BL.unlines
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
    expected =
      ( "OPTIMUM FOUND"
      , Just 232
      , Just $ array (1, 10) [(1, False), (2, False), (3, True), (4, True), (5, False), (6, True), (7, False), (8, True), (9, True), (10, False)]
      )

case_parsePBLog_SATISFIABLE :: Assertion
case_parsePBLog_SATISFIABLE = parsePBLog input @?= expected
  where
    input = BL.unlines
      [ "c foo"
      , "o 4750"
      , "o 232"
      , "s SATISFIABLE"
      , "c bar"
      , "v -x1 -x2 x3 x4 -x5"
      , "c baz"
      , "v x6 -x7 x8 x9 -x10"
      , "c quz"
      ]
    expected =
      ( "SATISFIABLE"
      , Just 232
      , Just $ array (1, 10) [(1, False), (2, False), (3, True), (4, True), (5, False), (6, True), (7, False), (8, True), (9, True), (10, False)]
      )

case_parsePBLog_UNSATISFIABLE :: Assertion
case_parsePBLog_UNSATISFIABLE = parsePBLog input @?= expected
  where
    input = BL.unlines
      [ "c foo"
      , "s UNSATISFIABLE"
      , "c bar"
      ]
    expected =
      ( "UNSATISFIABLE"
      , Nothing
      , Nothing
      )

case_parsePBLog_UNKNOWN :: Assertion
case_parsePBLog_UNKNOWN = parsePBLog input @?= expected
  where
    input = BL.unlines
      [ "c foo"
      , "s UNKNOWN"
      , "c bar"
      ]
    expected =
      ( "UNKNOWN"
      , Nothing
      , Nothing
      )

case_parsePBLog_UNKNOWN_implicit :: Assertion
case_parsePBLog_UNKNOWN_implicit = parsePBLog input @?= expected
  where
    input = BL.unlines ["c foo"]
    expected =
      ( "UNKNOWN"
      , Nothing
      , Nothing
      )

case_parsePBLog_UNSUPPORTED :: Assertion
case_parsePBLog_UNSUPPORTED = parsePBLog input @?= expected
  where
    input = BL.unlines
      [ "c foo"
      , "s UNSUPPORTED"
      , "c bar"
      ]
    expected =
      ( "UNSUPPORTED"
      , Nothing
      , Nothing
      )

-- ------------------------------------------------------------------------

satLogParserTestGroup :: TestTree
satLogParserTestGroup = $(testGroupGenerator)
