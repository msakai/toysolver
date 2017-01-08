{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.MIP (mipTestGroup) where

import Data.Maybe
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified ToySolver.Data.MIP.Solution.Gurobi as GurobiSol

case_GurobiSol :: Assertion
case_GurobiSol = do
  sol <- GurobiSol.readFile "samples/lp/test-solution-gurobi.sol"
  isJust (GurobiSol.solObjectiveValue sol) @?= True
  GurobiSol.parse (GurobiSol.render sol) @?= sol

mipTestGroup :: TestTree
mipTestGroup = $(testGroupGenerator)
