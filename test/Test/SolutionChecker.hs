{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.SolutionChecker  (solutionCheckerTestGroup) where

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH

import Data.Array.IArray

import qualified ToySolver.FileFormat.CNF as CNF
import ToySolver.Internal.SolutionChecker

-- ----------------------------------------------------------------------

case_checkSATResult_SATISFIABLE_ok :: Assertion
case_checkSATResult_SATISFIABLE_ok = do
  ok @?= True
  assertBool "messages should be empty" (null messages)
  where
    cnf = CNF.CNF
      { CNF.cnfNumVars = 2
      , CNF.cnfNumClauses = 3
      , CNF.cnfClauses =
          [ [1, 2]
          , [1, -2]
          , [-1, -2]
          ]
      }
    (ok, messages) = checkSATResult cnf ("SATISFIABLE", Just $ array (1, 2) [(1, True), (2, False)])

case_checkSATResult_SATISFIABLE_ng :: Assertion
case_checkSATResult_SATISFIABLE_ng = do
  ok @?= False
  assertBool "messages should not be empty" (not (null messages))
  where
    cnf = CNF.CNF
      { CNF.cnfNumVars = 2
      , CNF.cnfNumClauses = 3
      , CNF.cnfClauses =
          [ [1, 2]
          , [1, -2]
          , [-1, -2]
          ]
      }
    (ok, messages) = checkSATResult cnf ("SATISFIABLE", Just $ array (1, 2) [(1, False), (2, True)])

case_checkSATResult_UNSATISFIABLE_ok :: Assertion
case_checkSATResult_UNSATISFIABLE_ok = do
  ok @?= True
  assertBool "messages should be empty" (null messages)
  where
    cnf = CNF.CNF
      { CNF.cnfNumVars = 2
      , CNF.cnfNumClauses = 3
      , CNF.cnfClauses =
          [ [1, 2]
          , [1, -2]
          , [-1, 2]
          , [-1, -2]
          ]
      }
    (ok, messages) = checkSATResult cnf ("UNSATISFIABLE", Nothing)

case_checkSATResult_UNSATISFIABLE_ng :: Assertion
case_checkSATResult_UNSATISFIABLE_ng = do
  ok @?= False
  assertBool "messages should not be empty" (not (null messages))
  where
    cnf = CNF.CNF
      { CNF.cnfNumVars = 2
      , CNF.cnfNumClauses = 3
      , CNF.cnfClauses =
          [ [1, 2]
          , [1, -2]
          , [-1, 2]
          , [-1, -2]
          ]
      }
    (ok, messages) = checkSATResult cnf ("UNSATISFIABLE", Just $ array (1, 2) [(1, True), (2, True)])


case_checkSATResult_UNKNOWN_ok_1 :: Assertion
case_checkSATResult_UNKNOWN_ok_1 = do
  ok @?= True
  assertBool "messages should be empty" (null messages)
  where
    cnf = CNF.CNF
      { CNF.cnfNumVars = 2
      , CNF.cnfNumClauses = 3
      , CNF.cnfClauses =
          [ [1, 2]
          , [1, -2]
          , [-1, -2]
          ]
      }
    (ok, messages) = checkSATResult cnf ("UNKNOWN", Just $ array (1, 2) [(1, True), (2, False)])

case_checkSATResult_UNKNOWN_ok_2 :: Assertion
case_checkSATResult_UNKNOWN_ok_2 = do
  ok @?= True
  assertBool "messages should be empty" (null messages)
  where
    cnf = CNF.CNF
      { CNF.cnfNumVars = 2
      , CNF.cnfNumClauses = 3
      , CNF.cnfClauses =
          [ [1, 2]
          , [1, -2]
          , [-1, 2]
          ]
      }
    (ok, messages) = checkSATResult cnf ("UNKNOWN", Nothing)

case_checkSATResult_UNKNOWN_ng_1 :: Assertion
case_checkSATResult_UNKNOWN_ng_1 = do
  ok @?= False
  assertBool "messages should not be empty" (not (null messages))
  where
    cnf = CNF.CNF
      { CNF.cnfNumVars = 2
      , CNF.cnfNumClauses = 3
      , CNF.cnfClauses =
          [ [1, 2]
          , [1, -2]
          , [-1, 2]
          , [-1, -2]
          ]
      }
    (ok, messages) = checkSATResult cnf ("UNKNOWN", Just $ array (1, 2) [(1, True), (2, True)])

case_checkSATResult_bad_solution_status :: Assertion
case_checkSATResult_bad_solution_status = do
  ok @?= False
  assertBool "messages should not be empty" (not (null messages))
  where
    cnf = CNF.CNF
      { CNF.cnfNumVars = 2
      , CNF.cnfNumClauses = 3
      , CNF.cnfClauses =
          [ [1, 2]
          , [1, -2]
          , [-1, 2]
          ]
      }
    (ok, messages) = checkSATResult cnf ("FOO BAR", Just $ array (1, 2) [(1, True), (2, True)])

-- ----------------------------------------------------------------------
-- Test harness

solutionCheckerTestGroup :: TestTree
solutionCheckerTestGroup = $(testGroupGenerator)
