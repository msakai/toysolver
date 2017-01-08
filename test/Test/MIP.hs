{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
module Test.MIP (mipTestGroup) where

import Data.Maybe
import qualified Data.Map as Map
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified ToySolver.Data.MIP as MIP
import qualified ToySolver.Data.MIP.Solution.Gurobi as GurobiSol
import qualified ToySolver.Data.MIP.Solution.SCIP as SCIPSol

case_GurobiSol :: Assertion
case_GurobiSol = do
  sol <- GurobiSol.readFile "samples/lp/test-solution-gurobi.sol"
  isJust (GurobiSol.solObjectiveValue sol) @?= True
  GurobiSol.parse (GurobiSol.render sol) @?= sol

case_SCIPSol :: Assertion
case_SCIPSol = do
  (status,sol) <- SCIPSol.readFile "samples/lp/test-solution-scip.sol"
  status @?= "optimal solution found"
  sol @?=
    MIP.Solution
    { MIP.solObjectiveValue = Just 122.5
    , MIP.solVariables = Map.fromList [("x1", 40), ("x2", 10.5), ("x3", 19.5), ("x4", 3)]
    }

mipTestGroup :: TestTree
mipTestGroup = $(testGroupGenerator)
