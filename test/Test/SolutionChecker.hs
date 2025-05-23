{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.SolutionChecker  (solutionCheckerTestGroup) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Control.DeepSeq
import Control.Exception (evaluate)
import Control.Monad
import Data.Array.IArray
import Data.Default.Class
import qualified Data.Map.Lazy as Map
import qualified Data.PseudoBoolean as PBFile
import Data.Scientific (Scientific)
import qualified Numeric.Optimization.MIP as MIP

import qualified ToySolver.FileFormat.CNF as CNF
import ToySolver.Internal.SolutionChecker

-- ----------------------------------------------------------------------

checkOkAndEmpty :: HasCallStack => (Bool, [String]) -> Assertion
checkOkAndEmpty (ok, messages) = do
  _ <- evaluate $ force messages
  ok @?= True
  assertBool "messages should be empty" (null messages)

check :: HasCallStack => Bool -> (Bool, [String]) -> Assertion
check expected (ok, messages) = do
  _ <- evaluate $ force messages
  ok @?= expected
  unless ok $ assertBool "messages should not be empty" (not (null messages))

-- ----------------------------------------------------------------------

case_checkSATResult_SATISFIABLE :: Assertion
case_checkSATResult_SATISFIABLE = do
  checkOkAndEmpty $ checkSATResult cnf ("SATISFIABLE", Just $ array (1, 2) [(1, True), (2, False)])
  check False $ checkSATResult cnf ("SATISFIABLE", Just $ array (1, 2) [(1, False), (2, True)])
  check False $ checkSATResult cnf ("SATISFIABLE", Nothing)
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

case_checkSATResult_UNSATISFIABLE :: Assertion
case_checkSATResult_UNSATISFIABLE = do
  checkOkAndEmpty $ checkSATResult cnf ("UNSATISFIABLE", Nothing)
  check False $ checkSATResult cnf ("UNSATISFIABLE", Just $ array (1, 2) [(1, True), (2, True)])
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

case_checkSATResult_UNKNOWN :: Assertion
case_checkSATResult_UNKNOWN = do
  checkOkAndEmpty $ checkSATResult cnf ("UNKNOWN", Just $ array (1, 2) [(1, True), (2, False)])
  checkOkAndEmpty $ checkSATResult cnf ("UNKNOWN", Nothing)
  check False $ checkSATResult cnf ("UNKNOWN", Just $ array (1, 2) [(1, True), (2, True)])
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

case_checkSATResult_bad_solution_status :: Assertion
case_checkSATResult_bad_solution_status =
  check False $ checkSATResult cnf ("FOO BAR", Just $ array (1, 2) [(1, True), (2, True)])
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

-- ----------------------------------------------------------------------

case_checkMaxSATResult_SATISFIABLE :: Assertion
case_checkMaxSATResult_SATISFIABLE = do
  check True  $ checkMaxSATResult wcnf ("SATISFIABLE", Just 1, Just $ array (1, 2) [(1, True), (2, False)])
  check False $ checkMaxSATResult wcnf ("SATISFIABLE", Just 0, Just $ array (1, 2) [(1, True), (2, False)])
  check False $ checkMaxSATResult wcnf ("SATISFIABLE", Just 0, Just $ array (1, 2) [(1, False), (2, False)])
  check False $ checkMaxSATResult wcnf ("SATISFIABLE", Nothing, Nothing)
  where
    wcnf = CNF.WCNF
      { CNF.wcnfNumVars = 2
      , CNF.wcnfNumClauses = 3
      , CNF.wcnfTopCost = 100
      , CNF.wcnfClauses =
          [ (100, [1, 2])
          , (2, [1, -2])
          , (1, [-1, 2])
          , (3, [-1, -2])
          ]
      }

case_checkMaxSATResult_OPTIMUM_FOUND :: Assertion
case_checkMaxSATResult_OPTIMUM_FOUND = do
  check True  $ checkMaxSATResult wcnf ("OPTIMUM FOUND", Just 1, Just $ array (1, 2) [(1, True), (2, False)])
  check False $ checkMaxSATResult wcnf ("OPTIMUM FOUND", Just 0, Just $ array (1, 2) [(1, True), (2, False)])
  check False $ checkMaxSATResult wcnf ("OPTIMUM FOUND", Just 0, Just $ array (1, 2) [(1, False), (2, False)])
  check False $ checkMaxSATResult wcnf ("OPTIMUM FOUND", Nothing, Nothing)
  where
    wcnf = CNF.WCNF
      { CNF.wcnfNumVars = 2
      , CNF.wcnfNumClauses = 3
      , CNF.wcnfTopCost = 100
      , CNF.wcnfClauses =
          [ (100, [1, 2])
          , (2, [1, -2])
          , (1, [-1, 2])
          , (3, [-1, -2])
          ]
      }

case_checkMaxSATResult_UNSATISFIABLE :: Assertion
case_checkMaxSATResult_UNSATISFIABLE = do
  check True  $ checkMaxSATResult wcnf ("UNSATISFIABLE", Nothing, Nothing)
  check False $ checkMaxSATResult wcnf ("UNSATISFIABLE", Just 3, Just $ array (1, 2) [(1, True), (2, True)])
  where
    wcnf = CNF.WCNF
      { CNF.wcnfNumVars = 2
      , CNF.wcnfNumClauses = 3
      , CNF.wcnfTopCost = 100
      , CNF.wcnfClauses =
          [ (100, [1, 2])
          , (2, [1, -2])
          , (1, [-1, 2])
          , (3, [-1, -2])
          ]
      }

case_checkMaxSATResult_UNKNOWN :: Assertion
case_checkMaxSATResult_UNKNOWN = do
  check True  $ checkMaxSATResult wcnf ("UNKNOWN", Just 1, Just $ array (1, 2) [(1, True), (2, False)])
  check False $ checkMaxSATResult wcnf ("UNKNOWN", Just 0, Just $ array (1, 2) [(1, True), (2, False)])
  check True  $ checkMaxSATResult wcnf ("UNKNOWN", Nothing, Nothing)
  where
    wcnf = CNF.WCNF
      { CNF.wcnfNumVars = 2
      , CNF.wcnfNumClauses = 3
      , CNF.wcnfTopCost = 100
      , CNF.wcnfClauses =
          [ (100, [1, 2])
          , (2, [1, -2])
          , (1, [-1, 2])
          , (3, [-1, -2])
          ]
      }

case_checkMaxSATResult_bad_solution_status :: Assertion
case_checkMaxSATResult_bad_solution_status =
  check False $ checkMaxSATResult wcnf ("FOO BAR", Just 0, Just $ array (1, 2) [(1, True), (2, True)])
  where
    wcnf = CNF.WCNF
      { CNF.wcnfNumVars = 2
      , CNF.wcnfNumClauses = 3
      , CNF.wcnfTopCost = 100
      , CNF.wcnfClauses =
          [ (100, [1, 2])
          , (2, [1, -2])
          , (1, [-1, 2])
          , (3, [-1, -2])
          ]
      }

-- ----------------------------------------------------------------------

case_checkPBResult_SATISFIABLE :: Assertion
case_checkPBResult_SATISFIABLE = do
  check True  $ checkPBResult opb ("SATISFIABLE", Just 1, Just $ array (1, 2) [(1, True), (2, False)])
  check False $ checkPBResult opb ("SATISFIABLE", Just 0, Just $ array (1, 2) [(1, True), (2, False)])
  check False $ checkPBResult opb ("SATISFIABLE", Just 2, Just $ array (1, 2) [(1, False), (2, True)])
  check False $ checkPBResult opb ("SATISFIABLE", Nothing, Nothing)
  where
    (x1,x2) = (1,2)
    opb = PBFile.Formula
      { PBFile.pbNumVars = 2
      , PBFile.pbNumConstraints = 3
      , PBFile.pbObjectiveFunction = Just [(1, [x1]), (2, [x2])]
      , PBFile.pbConstraints =
          [ ([(1, [ x1]), (1, [ x2])], PBFile.Ge, 1)
          , ([(1, [ x1]), (1, [-x2])], PBFile.Ge, 1)
          , ([(1, [-x1]), (1, [-x2])], PBFile.Ge, 1)
          ]
      }

case_checkPBResult_OPTIMUM_FOUND :: Assertion
case_checkPBResult_OPTIMUM_FOUND = do
  check True  $ checkPBResult opb ("OPTIMUM FOUND", Just 1, Just $ array (1, 2) [(1, True), (2, False)])
  check False $ checkPBResult opb ("OPTIMUM FOUND", Just 0, Just $ array (1, 2) [(1, True), (2, False)])
  check False $ checkPBResult opb ("OPTIMUM FOUND", Just 2, Just $ array (1, 2) [(1, False), (2, True)])
  check False $ checkPBResult opb ("OPTIMUM FOUND", Nothing, Nothing)
  where
    (x1,x2) = (1,2)
    opb = PBFile.Formula
      { PBFile.pbNumVars = 2
      , PBFile.pbNumConstraints = 3
      , PBFile.pbObjectiveFunction = Just [(1, [x1]), (2, [x2])]
      , PBFile.pbConstraints =
          [ ([(1, [ x1]), (1, [ x2])], PBFile.Ge, 1)
          , ([(1, [ x1]), (1, [-x2])], PBFile.Ge, 1)
          , ([(1, [-x1]), (1, [-x2])], PBFile.Ge, 1)
          ]
      }

case_checkPBResult_UNSATISFIABLE :: Assertion
case_checkPBResult_UNSATISFIABLE = do
  check True  $ checkPBResult opb ("UNSATISFIABLE", Nothing, Nothing)
  check False $ checkPBResult opb ("UNSATISFIABLE", Just 3, Just $ array (1, 2) [(1, True), (2, True)])
  where
    (x1,x2) = (1,2)
    opb = PBFile.Formula
      { PBFile.pbNumVars = 2
      , PBFile.pbNumConstraints = 3
      , PBFile.pbObjectiveFunction = Just [(1, [x1]), (2, [x2])]
      , PBFile.pbConstraints =
          [ ([(1, [ x1]), (1, [ x2])], PBFile.Ge, 1)
          , ([(1, [ x1]), (1, [-x2])], PBFile.Ge, 1)
          , ([(1, [-x1]), (1, [-x2])], PBFile.Ge, 1)
          ]
      }

case_checkPBResult_UNKNOWN :: Assertion
case_checkPBResult_UNKNOWN = do
  check True  $ checkPBResult opb ("UNKNOWN", Just 1, Just $ array (1, 2) [(1, True), (2, False)])
  check True  $ checkPBResult opb ("UNKNOWN", Nothing, Nothing)
  check False $ checkPBResult opb ("UNKNOWN", Just 3, Just $ array (1, 2) [(1, True), (2, True)])
  where
    (x1,x2) = (1,2)
    opb = PBFile.Formula
      { PBFile.pbNumVars = 2
      , PBFile.pbNumConstraints = 3
      , PBFile.pbObjectiveFunction = Just [(1, [x1]), (2, [x2])]
      , PBFile.pbConstraints =
          [ ([(1, [ x1]), (1, [ x2])], PBFile.Ge, 1)
          , ([(1, [ x1]), (1, [-x2])], PBFile.Ge, 1)
          , ([(1, [-x1]), (1, [-x2])], PBFile.Ge, 1)
          ]
      }

case_checkPBResult_UNSUPPORTED :: Assertion
case_checkPBResult_UNSUPPORTED = do
  check True  $ checkPBResult opb ("UNSUPPORTED", Nothing, Nothing)
  where
    (x1,x2) = (1,2)
    opb = PBFile.Formula
      { PBFile.pbNumVars = 2
      , PBFile.pbNumConstraints = 3
      , PBFile.pbObjectiveFunction = Just [(1, [x1]), (2, [x2])]
      , PBFile.pbConstraints =
          [ ([(1, [ x1]), (1, [ x2])], PBFile.Ge, 1)
          , ([(1, [ x1]), (1, [-x2])], PBFile.Ge, 1)
          , ([(1, [-x1]), (1, [-x2])], PBFile.Ge, 1)
          ]
      }

case_checkPBResult_bad_solution_status :: Assertion
case_checkPBResult_bad_solution_status =
  check False $ checkPBResult opb ("FOO BAR", Just 3, Just $ array (1, 2) [(1, True), (2, True)])
  where
    (x1,x2) = (1,2)
    opb = PBFile.Formula
      { PBFile.pbNumVars = 2
      , PBFile.pbNumConstraints = 3
      , PBFile.pbObjectiveFunction = Just [(1, [x1]), (2, [x2])]
      , PBFile.pbConstraints =
          [ ([(1, [ x1]), (1, [ x2])], PBFile.Ge, 1)
          , ([(1, [ x1]), (1, [-x2])], PBFile.Ge, 1)
          , ([(1, [-x1]), (1, [-x2])], PBFile.Ge, 1)
          ]
      }

-- ----------------------------------------------------------------------

case_checkWBOResult_SATISFIABLE :: Assertion
case_checkWBOResult_SATISFIABLE = do
  check True  $ checkWBOResult wbo ("SATISFIABLE", Just 1, Just $ array (1, 2) [(1, True), (2, False)])
  check False $ checkWBOResult wbo ("SATISFIABLE", Just 0, Just $ array (1, 2) [(1, True), (2, False)])
  check False $ checkWBOResult wbo ("SATISFIABLE", Just 0, Just $ array (1, 2) [(1, False), (2, False)])
  check False $ checkWBOResult wbo ("SATISFIABLE", Just 2, Just $ array (1, 2) [(1, False), (2, True)])
  check False $ checkWBOResult wbo ("SATISFIABLE", Nothing, Nothing)
  where
    (x1,x2) = (1,2)
    wbo = PBFile.SoftFormula
      { PBFile.wboNumVars = 2
      , PBFile.wboNumConstraints = 3
      , PBFile.wboTopCost = Just 2
      , PBFile.wboConstraints =
          [ (Nothing, ([(1, [ x1]), (1, [ x2])], PBFile.Ge, 1))
          , (Just 2,  ([(1, [ x1]), (1, [-x2])], PBFile.Ge, 1))
          , (Just 1,  ([(1, [-x1]), (1, [ x2])], PBFile.Ge, 1))
          , (Just 3,  ([(1, [-x1]), (1, [-x2])], PBFile.Ge, 1))
          ]
      }

case_checkWBOResult_OPTIMUM_FOUND :: Assertion
case_checkWBOResult_OPTIMUM_FOUND = do
  check True  $ checkWBOResult wbo ("OPTIMUM FOUND", Just 1, Just $ array (1, 2) [(1, True), (2, False)])
  check False $ checkWBOResult wbo ("OPTIMUM FOUND", Just 0, Just $ array (1, 2) [(1, True), (2, False)])
  check False $ checkWBOResult wbo ("OPTIMUM FOUND", Just 0, Just $ array (1, 2) [(1, False), (2, False)])
  check False $ checkWBOResult wbo ("OPTIMUM FOUND", Just 2, Just $ array (1, 2) [(1, False), (2, True)])
  check False $ checkWBOResult wbo ("OPTIMUM FOUND", Nothing, Nothing)
  where
    (x1,x2) = (1,2)
    wbo = PBFile.SoftFormula
      { PBFile.wboNumVars = 2
      , PBFile.wboNumConstraints = 3
      , PBFile.wboTopCost = Just 2
      , PBFile.wboConstraints =
          [ (Nothing, ([(1, [ x1]), (1, [ x2])], PBFile.Ge, 1))
          , (Just 2,  ([(1, [ x1]), (1, [-x2])], PBFile.Ge, 1))
          , (Just 1,  ([(1, [-x1]), (1, [ x2])], PBFile.Ge, 1))
          , (Just 3,  ([(1, [-x1]), (1, [-x2])], PBFile.Ge, 1))
          ]
      }

case_checkWBOResult_UNSATISFIABLE :: Assertion
case_checkWBOResult_UNSATISFIABLE = do
  check True  $ checkWBOResult wbo ("UNSATISFIABLE", Nothing, Nothing)
  check False $ checkWBOResult wbo ("UNSATISFIABLE", Just 3, Just $ array (1, 2) [(1, True), (2, True)])
  where
    (x1,x2) = (1,2)
    wbo = PBFile.SoftFormula
      { PBFile.wboNumVars = 2
      , PBFile.wboNumConstraints = 3
      , PBFile.wboTopCost = Just 2
      , PBFile.wboConstraints =
          [ (Nothing, ([(1, [ x1]), (1, [ x2])], PBFile.Ge, 1))
          , (Just 2,  ([(1, [ x1]), (1, [-x2])], PBFile.Ge, 1))
          , (Just 1,  ([(1, [-x1]), (1, [ x2])], PBFile.Ge, 1))
          , (Just 3,  ([(1, [-x1]), (1, [-x2])], PBFile.Ge, 1))
          ]
      }

case_checkWBOResult_UNKNOWN :: Assertion
case_checkWBOResult_UNKNOWN = do
  check True  $ checkWBOResult wbo ("UNKNOWN", Just 1, Just $ array (1, 2) [(1, True), (2, False)])
  check False $ checkWBOResult wbo ("UNKNOWN", Just 0, Just $ array (1, 2) [(1, True), (2, False)])
  check True  $ checkWBOResult wbo ("UNKNOWN", Nothing, Nothing)
  where
    (x1,x2) = (1,2)
    wbo = PBFile.SoftFormula
      { PBFile.wboNumVars = 2
      , PBFile.wboNumConstraints = 3
      , PBFile.wboTopCost = Just 2
      , PBFile.wboConstraints =
          [ (Nothing, ([(1, [ x1]), (1, [ x2])], PBFile.Ge, 1))
          , (Just 2,  ([(1, [ x1]), (1, [-x2])], PBFile.Ge, 1))
          , (Just 1,  ([(1, [-x1]), (1, [ x2])], PBFile.Ge, 1))
          , (Just 3,  ([(1, [-x1]), (1, [-x2])], PBFile.Ge, 1))
          ]
      }

case_checkWBOResult_UNSUPPORTED :: Assertion
case_checkWBOResult_UNSUPPORTED = do
  check True  $ checkWBOResult wbo ("UNSUPPORTED", Nothing, Nothing)
  where
    (x1,x2) = (1,2)
    wbo = PBFile.SoftFormula
      { PBFile.wboNumVars = 2
      , PBFile.wboNumConstraints = 3
      , PBFile.wboTopCost = Just 2
      , PBFile.wboConstraints =
          [ (Nothing, ([(1, [ x1]), (1, [ x2])], PBFile.Ge, 1))
          , (Just 2,  ([(1, [ x1]), (1, [-x2])], PBFile.Ge, 1))
          , (Just 1,  ([(1, [-x1]), (1, [ x2])], PBFile.Ge, 1))
          , (Just 3,  ([(1, [-x1]), (1, [-x2])], PBFile.Ge, 1))
          ]
      }

case_checkWBOResult_bad_solution_status :: Assertion
case_checkWBOResult_bad_solution_status =
  check False $ checkWBOResult wbo ("FOO BAR", Just 0, Just $ array (1, 2) [(1, True), (2, True)])
  where
    (x1,x2) = (1,2)
    wbo = PBFile.SoftFormula
      { PBFile.wboNumVars = 2
      , PBFile.wboNumConstraints = 3
      , PBFile.wboTopCost = Just 2
      , PBFile.wboConstraints =
          [ (Nothing, ([(1, [ x1]), (1, [ x2])], PBFile.Ge, 1))
          , (Just 2,  ([(1, [ x1]), (1, [-x2])], PBFile.Ge, 1))
          , (Just 1,  ([(1, [-x1]), (1, [ x2])], PBFile.Ge, 1))
          , (Just 3,  ([(1, [-x1]), (1, [-x2])], PBFile.Ge, 1))
          ]
      }

-- ----------------------------------------------------------------------

case_checkMIPResult_objective_value :: Assertion
case_checkMIPResult_objective_value = do
  check True  $ checkMIPResult def prob sol{ MIP.solObjectiveValue = Just (8 + 1e-6) }
  check False $ checkMIPResult def prob sol{ MIP.solObjectiveValue = Just (8 + 1e-5) }

  where
    (x1, x2) = (MIP.varExpr "x1", MIP.varExpr "x2")

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
  check False $ checkMIPResult def prob (sol 0)
  check False $ checkMIPResult def prob (sol (10 - 1e-5))
  check True  $ checkMIPResult def prob (sol (10 - 1e-6))
  check True  $ checkMIPResult def prob (sol 10)
  check True  $ checkMIPResult def prob (sol 20)
  check True  $ checkMIPResult def prob (sol (20 + 1e-6))
  check False $ checkMIPResult def prob (sol (20 + 1e-5))
  check False $ checkMIPResult def prob (sol 25)
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
    check True  $ checkMIPResult def{ MIP.integralityTol = 1e-5 } (prob vt) sol
    check False $ checkMIPResult def{ MIP.integralityTol = 1e-6 } (prob vt) sol

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
    check True  $ checkMIPResult def (prob vt) (sol 0)
    check False $ checkMIPResult def (prob vt) (sol 5)
    check True  $ checkMIPResult def (prob vt) (sol 10)
    check False $ checkMIPResult def (prob vt) (sol 25)

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
  check True  $ checkMIPResult def prob sol
  check False $ checkMIPResult def{ MIP.feasibilityTol = 1e-7 } prob sol
  where
    (x1, x2) = (MIP.varExpr "x1", MIP.varExpr "x2")

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
  check True  $ checkMIPResult def (prob MIP.S1) (sol [0, 0, 0])
  check True  $ checkMIPResult def (prob MIP.S1) (sol [0, 1, 0])
  check False $ checkMIPResult def (prob MIP.S1) (sol [1, 0, 1])

  check True  $ checkMIPResult def (prob MIP.S2) (sol [0, 0, 0])
  check True  $ checkMIPResult def (prob MIP.S2) (sol [0, 1, 0])
  check True  $ checkMIPResult def (prob MIP.S2) (sol [1, 1, 0])
  check True  $ checkMIPResult def (prob MIP.S2) (sol [0, 1, 1])
  check False $ checkMIPResult def (prob MIP.S2) (sol [1, 0, 1])
  check False $ checkMIPResult def (prob MIP.S2) (sol [1, 1, 1])

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
