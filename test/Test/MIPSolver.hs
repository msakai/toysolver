{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
module Test.MIPSolver (mipSolverTestGroup) where

import Control.Monad
import Data.Default.Class
import qualified Data.Map as Map
import Test.Tasty
import Test.Tasty.HUnit
import qualified ToySolver.Data.MIP as MIP
import ToySolver.Data.MIP.Solver

-- ------------------------------------------------------------------------

case_cbc :: Assertion
case_cbc = do
  prob <- MIP.readFile def "samples/lp/test.lp"
  sol <- solve cbc def prob
  sol @?=
    MIP.Solution
    { MIP.solStatus = Just MIP.StatusOptimal
    , MIP.solObjectiveValue = Just 122.5
    , MIP.solVariables = Map.fromList [("x1", 40), ("x2", 10.5), ("x3", 19.5), ("x4", 3)]
    }

case_cbc_unbounded :: Assertion
case_cbc_unbounded = do
  prob <- MIP.readFile def "samples/lp/unbounded-ip.lp"
  sol <- solve cbc def prob
  let status = MIP.solStatus sol
  unless (status == Just MIP.StatusUnbounded || status == Just MIP.StatusInfeasibleOrUnbounded) $
    assertFailure $ unlines $
      [ "expected: Just StatusUnbounded or Just MIP.StatusInfeasibleOrUnbounded"
      , " but got: " ++ show status
      ]

case_cbc_infeasible :: Assertion
case_cbc_infeasible = do
  prob <- MIP.readFile def "samples/lp/infeasible.lp"
  sol <- solve cbc def prob
  MIP.solStatus sol @?= Just MIP.StatusInfeasible

-- ------------------------------------------------------------------------

case_cplex :: Assertion
case_cplex = do
  prob <- MIP.readFile def "samples/lp/test.lp"
  sol <- solve cplex def prob
  sol @?=
    MIP.Solution
    { MIP.solStatus = Just MIP.StatusOptimal
    , MIP.solObjectiveValue = Just 122.5
    , MIP.solVariables = Map.fromList [("x1", 40), ("x2", 10.5), ("x3", 19.5), ("x4", 3)]
    }

case_cplex_unbounded :: Assertion
case_cplex_unbounded = do
  prob <- MIP.readFile def "samples/lp/unbounded-ip.lp"
  sol <- solve cplex def prob
  let status = MIP.solStatus sol
  unless (status == Just MIP.StatusUnbounded || status == Just MIP.StatusInfeasibleOrUnbounded) $
    assertFailure $ unlines $
      [ "expected: Just StatusUnbounded or Just MIP.StatusInfeasibleOrUnbounded"
      , " but got: " ++ show status
      ]

case_cplex_infeasible :: Assertion
case_cplex_infeasible = do
  prob <- MIP.readFile def "samples/lp/infeasible.lp"
  sol <- solve cplex def prob
  MIP.solStatus sol @?= Just MIP.StatusInfeasible

-- ------------------------------------------------------------------------

case_glpsol :: Assertion
case_glpsol = do
  prob <- MIP.readFile def "samples/lp/test.lp"
  sol <- solve glpsol def prob
  sol @?=
    MIP.Solution
    { MIP.solStatus = Just MIP.StatusOptimal
    , MIP.solObjectiveValue = Just 122.5
    , MIP.solVariables = Map.fromList [("x1", 40), ("x2", 10.5), ("x3", 19.5), ("x4", 3)]
    }

case_glpsol_unbounded :: Assertion
case_glpsol_unbounded = do
  prob <- MIP.readFile def "samples/lp/unbounded-ip.lp"
  sol <- solve glpsol def prob
  let status = MIP.solStatus sol
  unless (status == Just MIP.StatusUnbounded || status == Just MIP.StatusInfeasibleOrUnbounded) $
    assertFailure $ unlines $
      [ "expected: Just StatusUnbounded or Just MIP.StatusInfeasibleOrUnbounded"
      , " but got: " ++ show status
      ]

case_glpsol_infeasible :: Assertion
case_glpsol_infeasible = do
  prob <- MIP.readFile def "samples/lp/infeasible.lp"
  sol <- solve glpsol def prob
  MIP.solStatus sol @?= Just MIP.StatusInfeasible

-- ------------------------------------------------------------------------

case_gurobiCl :: Assertion
case_gurobiCl = do
  prob <- MIP.readFile def "samples/lp/test.lp"
  sol <- solve gurobiCl def prob
  sol @?=
    MIP.Solution
    { MIP.solStatus = Just MIP.StatusOptimal
    , MIP.solObjectiveValue = Just 122.50000000000006
    , MIP.solVariables = Map.fromList [("x1", 40), ("x2", 10.5), ("x3", 19.500000000000018), ("x4", 3)]
    }

case_gurobiCl_unbounded :: Assertion
case_gurobiCl_unbounded = do
  prob <- MIP.readFile def "samples/lp/unbounded-ip.lp"
  sol <- solve gurobiCl def prob
  let status = MIP.solStatus sol
  unless (status == Just MIP.StatusUnbounded || status == Just MIP.StatusInfeasibleOrUnbounded) $
    assertFailure $ unlines $
      [ "expected: Just StatusUnbounded or Just MIP.StatusInfeasibleOrUnbounded"
      , " but got: " ++ show status
      ]

case_gurobiCl_infeasible :: Assertion
case_gurobiCl_infeasible = do
  prob <- MIP.readFile def "samples/lp/infeasible.lp"
  sol <- solve gurobiCl def prob
  MIP.solStatus sol @?= Just MIP.StatusInfeasible

-- ------------------------------------------------------------------------

case_lpSolve :: Assertion
case_lpSolve = do
  prob <- MIP.readFile def "samples/lp/test.lp"
  sol <- solve lpSolve def prob
  sol @?=
    MIP.Solution
    { MIP.solStatus = Just MIP.StatusOptimal
    , MIP.solObjectiveValue = Just 122.5
    , MIP.solVariables = Map.fromList [("x1", 40), ("x2", 10.5), ("x3", 19.5), ("x4", 3)]
    }

case_lpSolve_unbounded :: Assertion
case_lpSolve_unbounded = do
  prob <- MIP.readFile def "samples/lp/unbounded-ip.lp"
  sol <- solve lpSolve def prob
  let status = MIP.solStatus sol
  unless (status == Just MIP.StatusUnbounded || status == Just MIP.StatusInfeasibleOrUnbounded) $
    assertFailure $ unlines $
      [ "expected: Just StatusUnbounded or Just MIP.StatusInfeasibleOrUnbounded"
      , " but got: " ++ show status
      ]

case_lpSolve_infeasible :: Assertion
case_lpSolve_infeasible = do
  prob <- MIP.readFile def "samples/lp/infeasible.lp"
  sol <- solve lpSolve def prob
  MIP.solStatus sol @?= Just MIP.StatusInfeasible


-- ------------------------------------------------------------------------

case_scip :: Assertion
case_scip = do
  prob <- MIP.readFile def "samples/lp/test.lp"
  sol <- solve scip def prob
  sol @?=
    MIP.Solution
    { MIP.solStatus = Just MIP.StatusOptimal
    , MIP.solObjectiveValue = Just 122.5
    , MIP.solVariables = Map.fromList [("x1", 40), ("x2", 10.5), ("x3", 19.5), ("x4", 3)]
    }

case_scip_unbounded :: Assertion
case_scip_unbounded = do
  prob <- MIP.readFile def "samples/lp/unbounded-ip.lp"
  sol <- solve scip def prob
  let status = MIP.solStatus sol
  unless (status == Just MIP.StatusUnbounded || status == Just MIP.StatusInfeasibleOrUnbounded) $
    assertFailure $ unlines $
      [ "expected: Just StatusUnbounded or Just MIP.StatusInfeasibleOrUnbounded"
      , " but got: " ++ show status
      ]

case_scip_infeasible :: Assertion
case_scip_infeasible = do
  prob <- MIP.readFile def "samples/lp/infeasible.lp"
  sol <- solve scip def prob
  MIP.solStatus sol @?= Just MIP.StatusInfeasible

-- ------------------------------------------------------------------------

mipSolverTestGroup :: TestTree
mipSolverTestGroup = testGroup "Test.MIPSolver" $ []
#ifdef TEST_CBC
  ++
  [ testCase "cbc" case_cbc
  , testCase "cbc unbounded" case_cbc_unbounded
  , testCase "cbc infeasible" case_cbc_infeasible
  ]
#endif
#ifdef TEST_CPLEX
  ++
  [ testCase "cplex" case_cplex
  , testCase "cplex unbounded" case_cplex_unbounded
  , testCase "cplex infeasible" case_cplex_infeasible
  ]
#endif
#ifdef TEST_GLPSOL
  ++
  [ testCase "glpsol" case_glpsol
  , testCase "glpsol unbounded" case_glpsol_unbounded
  , testCase "glpsol infeasible" case_glpsol_infeasible
  ]
#endif
#ifdef TEST_GUROBI_CL
  ++
  [ testCase "gurobiCl" case_gurobiCl
  , testCase "gurobiCl unbounded" case_gurobiCl_unbounded
  , testCase "gurobiCl infeasible" case_gurobiCl_infeasible
  ]
#endif
#ifdef TEST_LP_SOLVE
  ++
  [ testCase "lpSolve" case_lpSolve
  , testCase "lpSolve unbounded" case_lpSolve_unbounded
  , testCase "lpSolve infeasible" case_lpSolve_infeasible
  ]
#endif
#ifdef TEST_SCIP
  ++
  [ testCase "scip" case_scip
  , testCase "scip unbounded" case_scip_unbounded
  , testCase "scip infeasible" case_scip_infeasible
  ]
#endif

