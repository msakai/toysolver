{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
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
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.SLS.ProbSAT as ProbSAT
import qualified ToySolver.Text.CNF as CNF
import qualified ToySolver.Text.MaxSAT as MaxSAT

arbitraryCNF :: Gen CNF.CNF
arbitraryCNF = do
  nv <- choose (0,10)
  nc <- choose (0,50)
  cs <- replicateM nc $ do
    len <- choose (0,10)
    if nv == 0 then
      return $ SAT.packClause []
    else
      SAT.packClause <$> (replicateM len $ choose (-nv, nv) `suchThat` (/= 0))
  return $
    CNF.CNF
    { CNF.numVars = nv
    , CNF.numClauses = nc
    , CNF.clauses = cs
    }

evalCNFCost :: SAT.Model -> CNF.CNF -> Int
evalCNFCost m cnf = sum $ map f (CNF.clauses cnf)
  where
    f c = if SAT.evalClause m (SAT.unpackClause c) then 0 else 1

arbitraryWCNF :: Gen MaxSAT.WCNF
arbitraryWCNF = do
  nv <- choose (0,10)
  nc <- choose (0,50)
  cs <- replicateM nc $ do
    len <- choose (0,10)
    w <- arbitrary
    c <- do
      if nv == 0 then do
        return $ SAT.packClause []
      else do
        SAT.packClause <$> (replicateM len $ choose (-nv, nv) `suchThat` (/= 0))
    return (fmap getPositive w, c)
  let topCost = sum [w | (Just w, _) <- cs] + 1
  return $
    MaxSAT.WCNF
    { MaxSAT.numVars = nv
    , MaxSAT.numClauses = nc
    , MaxSAT.topCost = topCost
    , MaxSAT.clauses = [(fromMaybe topCost w, c) | (w,c) <- cs]
    }

evalWCNFCost :: SAT.Model -> MaxSAT.WCNF -> Integer
evalWCNFCost m wcnf = sum $ do
  (w,c) <- MaxSAT.clauses wcnf
  guard $ not $ SAT.evalClause m (SAT.unpackClause c)
  return w

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
  QM.assert (bounds sol == (1, CNF.numVars cnf))
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
  QM.assert (bounds sol == (1, MaxSAT.numVars wcnf))
  QM.assert (obj == evalWCNFCost sol wcnf)

case_probSAT_case1 :: Assertion
case_probSAT_case1 = do
  let cnf =
        CNF.CNF
        { CNF.numVars = 1
        , CNF.numClauses = 2
        , CNF.clauses = map SAT.packClause
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
