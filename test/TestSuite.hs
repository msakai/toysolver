module Main where

import Test.Tasty (defaultMain, testGroup)

import TestAReal
import TestArith
import TestCongruenceClosure
import TestContiTraverso
import TestFiniteModelFinder
import TestLPFile
import TestMIPSolver2
import TestMPSFile
import TestSDPFile
import TestMisc
import TestSAT
import TestSimplex
import TestSimplex2

main :: IO ()
main = defaultMain $ testGroup "ToySolver test suite"
  [ arealTestGroup
  , arithTestGroup
  , ccTestGroup
  , ctTestGroup
  , fmfTestGroup
  , lpTestGroup
  , miscTestGroup
  , mipSolver2TestGroup
  , mpsTestGroup
  , satTestGroup
  , sdpTestGroup
  , simplexTestGroup
  , simplex2TestGroup
  ]
