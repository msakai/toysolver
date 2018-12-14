{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Test.QBF (qbfTestGroup) where

import Control.Monad
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Maybe (catMaybes)

import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import ToySolver.Data.Boolean
import qualified ToySolver.Data.BoolExpr as BoolExpr
import qualified ToySolver.QBF as QBF

-- -------------------------------------------------------------------

prop_solveCEGAR :: Property
prop_solveCEGAR = QM.monadicIO $ do
  (nv, prefix@(_ : prefix'), matrix) <- QM.pick arbitrarySmallQBF
  (sat, cert) <- QM.run $ QBF.solveCEGAR nv prefix matrix
  QM.assert $ sat == evalQBFNaive prefix matrix
  case cert of
    Nothing -> return ()
    Just ls ->
      QM.assert $ sat == evalQBFNaive' (IntMap.fromList [(abs lit, lit > 0) | lit <- IntSet.toList ls]) prefix' matrix

prop_solveCEGARIncremental :: Property
prop_solveCEGARIncremental = QM.monadicIO $ do
  (nv, prefix@(_ : prefix'), matrix) <- QM.pick arbitrarySmallQBF
  (sat, cert) <- QM.run $ QBF.solveCEGARIncremental nv prefix matrix
  QM.assert $ sat == evalQBFNaive prefix matrix
  case cert of
    Nothing -> return ()
    Just ls ->
      QM.assert $ sat == evalQBFNaive' (IntMap.fromList [(abs lit, lit > 0) | lit <- IntSet.toList ls]) prefix' matrix

prop_solveQE :: Property
prop_solveQE = QM.monadicIO $ do
  (nv, prefix@(_ : prefix'), matrix) <- QM.pick arbitrarySmallQBF
  (sat, cert) <- QM.run $ QBF.solveQE nv prefix matrix
  QM.assert $ sat == evalQBFNaive prefix matrix
  case cert of
    Nothing -> return ()
    Just ls ->
      QM.assert $ sat == evalQBFNaive' (IntMap.fromList [(abs lit, lit > 0) | lit <- IntSet.toList ls]) prefix' matrix

{-
If the innermost quantifier is a universal quantifier,
we can remove the bound variable v from the clauses that
do not contain v and ¬v simultaneously.
-}
prop_eliminate_last_universal_quantifier :: Property
prop_eliminate_last_universal_quantifier = QM.monadicIO $ do
  (nv, prefix, matrix1) <- QM.pick gen
  let (QBF.A, xs) = last prefix
      matrix2 = [[lit | lit <- clause, abs lit `IntSet.notMember` xs] | clause <- matrix1]
      matrix1' = andB [orB [f lit | lit <- clause] | clause <- matrix1]
      matrix2' = andB [orB [f lit | lit <- clause] | clause <- matrix2]
      f lit = if lit > 0
              then BoolExpr.Atom lit
              else notB (BoolExpr.Atom (abs lit))
  (sat1, cert1) <- QM.run $ QBF.solveCEGAR nv prefix matrix1'
  (sat2, cert2) <- QM.run $ QBF.solveCEGAR nv (init prefix) matrix2'
  QM.assert $ sat1 == sat2
  where
    gen :: Gen (Int, QBF.Prefix, [[Int]])
    gen = do
      nv <- choose (0,10)
      nc <- choose (0,50)
      let vs = [1..nv]
      q1 <- arbitrary
      q2 <- arbitrary
      vs1 <- IntSet.fromList <$> subsetof vs
      vs2 <- IntSet.fromList <$> subsetof vs    
      matrix <- replicateM nc $ do
        if nv == 0 then
          return []
        else do
          mapM (\v -> elements [v, -v]) =<< subsetof vs
      return
        ( nv
        , [(q1,vs1), (q2, vs2 IntSet.\\ vs1), (QBF.A, IntSet.fromList vs IntSet.\\ (vs1 `IntSet.union` vs2))]
        , matrix
        )

-- -------------------------------------------------------------------

evalQBFNaive :: QBF.Prefix -> QBF.Matrix -> Bool
evalQBFNaive prefix = evalQBFNaive' IntMap.empty prefix

evalQBFNaive' :: IntMap Bool -> QBF.Prefix -> QBF.Matrix -> Bool
evalQBFNaive' env prefix = f env [(q,v) | (q,vs) <- prefix, v <- IntSet.toList vs]
  where
    f env [] matrix = BoolExpr.fold (env IntMap.!) matrix
    f env ((QBF.A,x) : prefix) matrix =
      f (IntMap.insert x True  env) prefix matrix &&
      f (IntMap.insert x False env) prefix matrix
    f env ((QBF.E,x) : prefix) matrix =
      f (IntMap.insert x True  env) prefix matrix ||
      f (IntMap.insert x False env) prefix matrix

-- -------------------------------------------------------------------

subsetof :: [a] -> Gen [a]
subsetof xs = catMaybes <$> sequence [elements [Just x, Nothing] | x <- xs]

arbitrarySmallQBF :: Gen (Int, QBF.Prefix, QBF.Matrix)
arbitrarySmallQBF = do
  (nv, prefix, matrix') <- arbitrarySmallQBF'
  let f lit = if lit > 0
              then BoolExpr.Atom lit
              else notB (BoolExpr.Atom (abs lit))
      matrix = andB [orB [f lit | lit <- clause] | clause <- matrix']
  return (nv, prefix, matrix)

arbitrarySmallQBF' :: Gen (Int, QBF.Prefix, [[Int]])
arbitrarySmallQBF' = do
  nv <- choose (0,10)
  nc <- choose (0,50)

  let vs = [1..nv]
  q1 <- arbitrary
  q2 <- arbitrary
  q3 <- arbitrary
  vs1 <- IntSet.fromList <$> subsetof vs
  vs2 <- IntSet.fromList <$> subsetof vs

  matrix <- replicateM nc $ do
    len <- choose (0,10)
    if nv == 0 then
      return []
    else
      replicateM len $ choose (-nv, nv) `suchThat` (/= 0)
  
  return
    ( nv
    , [(q1,vs1), (q2, vs2 IntSet.\\ vs1), (q3, IntSet.fromList vs IntSet.\\ (vs1 `IntSet.union` vs2))]
    , matrix
    )

instance Arbitrary QBF.Quantifier where
  arbitrary = arbitraryBoundedEnum

-- -------------------------------------------------------------------
-- Test harness

qbfTestGroup :: TestTree
qbfTestGroup = $(testGroupGenerator)
