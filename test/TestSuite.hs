module Main where

import Test.Tasty (defaultMain, testGroup)

import Test.AReal
import Test.AReal2
import Test.Arith
import Test.BitVector
import Test.BoolExpr
import Test.CongruenceClosure
import Test.ContiTraverso
import Test.Delta
import Test.FiniteModelFinder
import Test.GraphShortestPath
import Test.HittingSets
import Test.Knapsack
import Test.LPFile
import Test.MIP
import Test.MIPSolver
import Test.MIPSolver2
import Test.MPSFile
import Test.ProbSAT
import Test.SDPFile
import Test.Misc
import Test.QBF
import Test.SAT
import Test.Simplex
import Test.SimplexTextbook
import Test.SMT
import Test.SMTLIB2Solver
import Test.Smtlib
import Test.SubsetSum
import Test.BipartiteMatching

main :: IO ()
main = defaultMain $ testGroup "ToySolver test suite"
  [ arealTestGroup
--  , areal2TestGroup
  , arithTestGroup
  , bitVectorTestGroup
  , boolExprTestGroup
  , ccTestGroup
  , ctTestGroup
  , deltaTestGroup
  , fmfTestGroup
  , graphShortestPathTestGroup
  , hittingSetsTestGroup
  , knapsackTestGroup
  , lpTestGroup
  , miscTestGroup
  , mipTestGroup
  , mipSolverTestGroup
  , mipSolver2TestGroup
  , mpsTestGroup
  , probSATTestGroup
  , qbfTestGroup
  , satTestGroup
  , sdpTestGroup
  , simplexTestGroup
  , simplexTextbookTestGroup
  , smtTestGroup
  , smtlib2SolverTestGroup
  , smtlibTestGroup
  , subsetSumTestGroup
  , bipartiteMatchingTestGroup
  ]
