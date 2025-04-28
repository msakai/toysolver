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

import Control.DeepSeq
import Control.Exception (evaluate)
import Control.Monad
import Data.Array.IArray
import Data.Default.Class
import qualified Data.Map.Lazy as Map
import Data.Scientific (Scientific)
import qualified Numeric.Optimization.MIP as MIP

import qualified ToySolver.FileFormat.CNF as CNF
import ToySolver.Internal.SolutionChecker

-- ----------------------------------------------------------------------

case_checkSATResult_SATISFIABLE_ok :: Assertion
case_checkSATResult_SATISFIABLE_ok = do
  ok @?= True
  _ <- evaluate $ force messages
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

case_checkSATResult_SATISFIABLE_ng_1 :: Assertion
case_checkSATResult_SATISFIABLE_ng_1 = do
  ok @?= False
  _ <- evaluate $ force messages
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

case_checkSATResult_SATISFIABLE_ng_2 :: Assertion
case_checkSATResult_SATISFIABLE_ng_2 = do
  ok @?= False
  _ <- evaluate $ force messages
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
    (ok, messages) = checkSATResult cnf ("SATISFIABLE", Nothing)

case_checkSATResult_UNSATISFIABLE_ok :: Assertion
case_checkSATResult_UNSATISFIABLE_ok = do
  ok @?= True
  _ <- evaluate $ force messages
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
  _ <- evaluate $ force messages
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
  _ <- evaluate $ force messages
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
  _ <- evaluate $ force messages
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
  _ <- evaluate $ force messages
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
  _ <- evaluate $ force messages
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

case_checkMIPResult_objective_value :: Assertion
case_checkMIPResult_objective_value = do
  fst (checkMIPResult def prob sol{ MIP.solObjectiveValue = Just (8 + 1e-6) }) @?= True
  fst (checkMIPResult def prob sol{ MIP.solObjectiveValue = Just (8 + 1e-5) }) @?= False

  where
    [x1, x2] = map MIP.varExpr ["x1", "x2"]

    prob :: MIP.Problem Scientific
    prob = def
      { MIP.objectiveFunction = def{ MIP.objExpr = 2*x1 + 3*x2 }
      , MIP.varDomains = Map.fromList
          [ ("x1", (MIP.ContinuousVariable, MIP.defaultBounds))
          , ("x2", (MIP.ContinuousVariable, MIP.defaultBounds))
          ]
      }

    sol :: MIP.Solution Scientific
    sol = def
      { MIP.solStatus = MIP.StatusFeasible
      , MIP.solObjectiveValue = Just 8
      , MIP.solVariables = Map.fromList
          [ ("x1", 1)
          , ("x2", 2)
          ]
      }

case_checkMIPResult_variable_bounds :: Assertion
case_checkMIPResult_variable_bounds = do
  fst (checkMIPResult def prob (sol 0)) @?= False
  fst (checkMIPResult def prob (sol (10 - 1e-5))) @?= False
  fst (checkMIPResult def prob (sol (10 - 1e-6))) @?= True
  fst (checkMIPResult def prob (sol 10)) @?= True
  fst (checkMIPResult def prob (sol 20)) @?= True
  fst (checkMIPResult def prob (sol (20 + 1e-6))) @?= True
  fst (checkMIPResult def prob (sol (20 + 1e-5))) @?= False
  fst (checkMIPResult def prob (sol 25)) @?= False
  where
    prob :: MIP.Problem Scientific
    prob = def
      { MIP.varDomains = Map.singleton "x" (MIP.ContinuousVariable, (10, 20))
      }

    sol :: Scientific -> MIP.Solution Scientific
    sol val = def
      { MIP.solStatus = MIP.StatusFeasible
      , MIP.solObjectiveValue = Nothing
      , MIP.solVariables = Map.singleton "x" val
      }

case_checkMIPResult_integrality :: Assertion
case_checkMIPResult_integrality = do
  forM_ ([MIP.IntegerVariable, MIP.SemiIntegerVariable] :: [MIP.VarType]) $ \vt -> do
    fst (checkMIPResult def{ MIP.integralityTol = 1e-5 } (prob vt) sol) @?= True
    fst (checkMIPResult def{ MIP.integralityTol = 1e-6 } (prob vt) sol) @?= False

  where
    prob :: MIP.VarType -> MIP.Problem Scientific
    prob vt = def
      { MIP.varDomains = Map.singleton "x" (vt, (1, 2))
      }

    sol :: MIP.Solution Scientific
    sol = def
      { MIP.solStatus = MIP.StatusFeasible
      , MIP.solObjectiveValue = Nothing
      , MIP.solVariables = Map.singleton "x" (1 + 1e-5)
      }

case_checkMIPResult_semi :: Assertion
case_checkMIPResult_semi = do
  forM_ ([MIP.SemiContinuousVariable, MIP.SemiIntegerVariable] :: [MIP.VarType]) $ \vt -> do
    fst (checkMIPResult def (prob vt) (sol 0)) @?= True
    fst (checkMIPResult def (prob vt) (sol 5)) @?= False
    fst (checkMIPResult def (prob vt) (sol 10)) @?= True
    fst (checkMIPResult def (prob vt) (sol 25)) @?= False

  where
    prob :: MIP.VarType -> MIP.Problem Scientific
    prob vt = def
      { MIP.varDomains = Map.singleton "x" (vt, (10, 20))
      }

    sol :: Scientific -> MIP.Solution Scientific
    sol val = def
      { MIP.solStatus = MIP.StatusFeasible
      , MIP.solObjectiveValue = Nothing
      , MIP.solVariables = Map.singleton "x" val
      }

case_checkMIPResult_constraints :: Assertion
case_checkMIPResult_constraints = do
  fst (checkMIPResult def prob sol) @?= True
  fst (checkMIPResult def{ MIP.feasibilityTol = 1e-7 } prob sol) @?= False
  where
    [x1, x2] = map MIP.varExpr ["x1", "x2"]

    prob :: MIP.Problem Scientific
    prob = def
      { MIP.constraints =
          [ x1 - x2 MIP..<=. 0
          ]
      , MIP.varDomains = Map.fromList
          [ ("x1", (MIP.ContinuousVariable, MIP.defaultBounds))
          , ("x2", (MIP.ContinuousVariable, MIP.defaultBounds))
          ]
      }

    sol :: MIP.Solution Scientific
    sol = def
      { MIP.solStatus = MIP.StatusFeasible
      , MIP.solObjectiveValue = Nothing
      , MIP.solVariables = Map.fromList
          [ ("x1", 1)
          , ("x2", 1 - 1e-6)
          ]
      }

case_checkMIPResult_SOS_constraints :: Assertion
case_checkMIPResult_SOS_constraints = do
  fst (checkMIPResult def (prob MIP.S1) (sol [0, 0, 0])) @?= True
  fst (checkMIPResult def (prob MIP.S1) (sol [0, 1, 0])) @?= True
  fst (checkMIPResult def (prob MIP.S1) (sol [1, 0, 1])) @?= False
  fst (checkMIPResult def (prob MIP.S2) (sol [0, 0, 0])) @?= True
  fst (checkMIPResult def (prob MIP.S2) (sol [0, 1, 0])) @?= True
  fst (checkMIPResult def (prob MIP.S2) (sol [1, 1, 0])) @?= True
  fst (checkMIPResult def (prob MIP.S2) (sol [0, 1, 1])) @?= True
  fst (checkMIPResult def (prob MIP.S2) (sol [1, 0, 1])) @?= False
  fst (checkMIPResult def (prob MIP.S2) (sol [1, 1, 1])) @?= False

  where
    prob :: MIP.SOSType -> MIP.Problem Scientific
    prob t = def
      { MIP.varDomains = Map.fromList
          [ (x, (MIP.IntegerVariable, (0, 1)))
          | x <- ["x1", "x2", "x3"]
          ]
      , MIP.sosConstraints =
          [ MIP.SOSConstraint
            { MIP.sosLabel = Nothing
            , MIP.sosType = t
            , MIP.sosBody = [("x1", 1), ("x2", 2), ("x3", 3)]
            }
          ]
      }

    sol :: [Scientific] -> MIP.Solution Scientific
    sol xs = def
      { MIP.solStatus = MIP.StatusFeasible
      , MIP.solObjectiveValue = Nothing
      , MIP.solVariables = Map.fromList $ zip ["x1", "x2", "x3"] xs
      }

-- ----------------------------------------------------------------------
-- Test harness

solutionCheckerTestGroup :: TestTree
solutionCheckerTestGroup = $(testGroupGenerator)
