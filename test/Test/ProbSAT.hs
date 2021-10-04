{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.ProbSAT (probSATTestGroup) where

import Control.Applicative
import Control.Monad
import Data.Array.IArray
import Data.Default.Class
import Data.Maybe
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM
import Test.QuickCheck.Modifiers
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Solver.SLS.ProbSAT as ProbSAT

import Test.SAT.Utils


prop_probSAT :: Property
prop_probSAT = QM.monadicIO $ do
  cnf <- QM.pick arbitraryCNF
  opt <- QM.pick $ do
    target <- choose (0, 10)
    maxTries <- choose (0, 10)
    maxFlips <- choose (0, 1000)
    return $
      def
      { ProbSAT.optTarget   = target
      , ProbSAT.optMaxTries = maxTries
      , ProbSAT.optMaxFlips = maxFlips
      }
  (obj,sol) <- QM.run $ do
    solver <- ProbSAT.newSolver cnf
    let cb = 3.6
        cm = 0.5
        f make break = cm**make / cb**break
    ProbSAT.probsat solver opt def f
    ProbSAT.getBestSolution solver
  QM.monitor (counterexample (show (obj,sol)))
  QM.assert (bounds sol == (1, CNF.cnfNumVars cnf))
  QM.assert (obj == fromIntegral (evalCNFCost sol cnf))

prop_probSAT_weighted :: Property
prop_probSAT_weighted = QM.monadicIO $ do
  wcnf <- QM.pick arbitraryWCNF
  opt <- QM.pick $ do
    target <- choose (0, 10)
    maxTries <- choose (0, 10)
    maxFlips <- choose (0, 1000)
    return $
      def
      { ProbSAT.optTarget   = target
      , ProbSAT.optMaxTries = maxTries
      , ProbSAT.optMaxFlips = maxFlips
      }
  (obj,sol) <- QM.run $ do
    solver <- ProbSAT.newSolverWeighted wcnf
    let cb = 3.6
        cm = 0.5
        f make break = cm**make / cb**break
    ProbSAT.probsat solver opt def f
    ProbSAT.getBestSolution solver
  QM.monitor (counterexample (show (obj,sol)))
  QM.assert (bounds sol == (1, CNF.wcnfNumVars wcnf))
  QM.assert (obj == evalWCNFCost sol wcnf)

case_probSAT_case1 :: Assertion
case_probSAT_case1 = do
  let cnf =
        CNF.CNF
        { CNF.cnfNumVars = 1
        , CNF.cnfNumClauses = 2
        , CNF.cnfClauses = map SAT.packClause
            [ [1,-1]
            , []
            ]
        }
  solver <- ProbSAT.newSolver cnf
  let opt =
        def
        { ProbSAT.optTarget   = 0
        , ProbSAT.optMaxTries = 1
        , ProbSAT.optMaxFlips = 10
        }
      cb = 3.6
      cm = 0.5
      f make break = cm**make / cb**break
  ProbSAT.probsat solver opt def f

------------------------------------------------------------------------
-- Test harness

probSATTestGroup :: TestTree
probSATTestGroup = $(testGroupGenerator)
