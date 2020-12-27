module Main where

import Test.Tasty (defaultMain, testGroup)

import Test.AReal
import Test.AReal2
import Test.Arith
import Test.BitVector
import Test.BoolExpr
import Test.CongruenceClosure
import Test.ContiTraverso
import Test.Converter
import Test.CNF
import Test.Delta
import Test.FiniteModelFinder
import Test.GraphShortestPath
import Test.HittingSets
import Test.Knapsack
import Test.MIPSolver
import Test.ProbSAT
import Test.SDPFile
import Test.Misc
import Test.QBF
import Test.QUBO
import Test.SAT
import Test.SAT.Encoder
import Test.SAT.ExistentialQuantification
import Test.SAT.MUS
import Test.SAT.TheorySolver
import Test.SAT.Types
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
  , cnfTestGroup
  , converterTestGroup
  , ctTestGroup
  , deltaTestGroup
  , fmfTestGroup
  , graphShortestPathTestGroup
  , hittingSetsTestGroup
  , knapsackTestGroup
  , miscTestGroup
  , mipSolverTestGroup
  , probSATTestGroup
  , qbfTestGroup
  , quboTestGroup
  , satTestGroup
  , satEncoderTestGroup
  , satExistentialQuantificationTestGroup
  , satMUSTestGroup
  , satTheorySolverTestGroup
  , satTypesTestGroup
  , sdpTestGroup
  , simplexTestGroup
  , simplexTextbookTestGroup
  , smtTestGroup
  , smtlib2SolverTestGroup
  , smtlibTestGroup
  , subsetSumTestGroup
  , bipartiteMatchingTestGroup
  ]
