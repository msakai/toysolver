module Main where

import Test.Tasty (defaultMain, testGroup)

import Test.AReal
import Test.AReal2
import Test.Arith
import Test.BoolExpr
import Test.CongruenceClosure
import Test.ContiTraverso
import Test.Delta
import Test.FiniteModelFinder
import Test.HittingSets
import Test.Knapsack
import Test.LPFile
import Test.MIPSolver2
import Test.MPSFile
import Test.SDPFile
import Test.Misc
import Test.QBF
import Test.SAT
import Test.Simplex
import Test.Simplex2
import Test.SMT
import Test.SMTLIB2Solver
import Test.Smtlib
import Test.SubsetSum

main :: IO ()
main = defaultMain $ testGroup "ToySolver test suite"
  [ arealTestGroup
--  , areal2TestGroup
  , arithTestGroup
  , boolExprTestGroup
  , ccTestGroup
  , ctTestGroup
  , deltaTestGroup
  , fmfTestGroup
  , hittingSetsTestGroup
  , knapsackTestGroup
  , lpTestGroup
  , miscTestGroup
  , mipSolver2TestGroup
  , mpsTestGroup
  , qbfTestGroup
  , satTestGroup
  , sdpTestGroup
  , simplexTestGroup
  , simplex2TestGroup
  , smtTestGroup
  , smtlib2SolverTestGroup
  , smtlibTestGroup
  , subsetSumTestGroup
  ]
