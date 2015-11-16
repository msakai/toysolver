module Main where

import Test.Tasty (defaultMain, testGroup)

import Test.AReal
import Test.AReal2
import Test.Arith
import Test.CongruenceClosure
import Test.ContiTraverso
import Test.FiniteModelFinder
import Test.LPFile
import Test.MIPSolver2
import Test.MPSFile
import Test.SDPFile
import Test.Misc
import Test.SAT
import Test.Simplex
import Test.Simplex2
import Test.SMT

main :: IO ()
main = defaultMain $ testGroup "ToySolver test suite"
  [ arealTestGroup
--  , areal2TestGroup
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
  , smtTestGroup
  ]
