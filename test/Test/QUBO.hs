{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, FlexibleContexts #-}
module Test.QUBO (quboTestGroup) where

import Control.Monad
import Data.Array.IArray
import qualified Data.IntMap.Strict as IntMap
    
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import ToySolver.Converter
import qualified ToySolver.QUBO as QUBO
import ToySolver.Converter.QUBO

------------------------------------------------------------------------

instance (Arbitrary a, Eq a, Num a) => Arbitrary (QUBO.Problem a) where
  arbitrary = do
    nv <- choose (1,10)
    m <- choose (0,nv*nv)
    jj <- liftM (f . IntMap.unionsWith (IntMap.unionWith (+))) $ replicateM m $ do
      i <- choose (0,nv-1)
      j <- choose (i,nv-1)
      jj_ij <- arbitrary
      return $ IntMap.singleton i $ IntMap.singleton j jj_ij
    return $
      QUBO.Problem
      { QUBO.quboNumVars = nv
      , QUBO.quboMatrix = jj
      }
    where
      f = IntMap.mapMaybe (g . IntMap.filter (/= 0))
      g m = if IntMap.null m then Nothing else Just m

arbitrarySolution :: Int -> Gen QUBO.Solution
arbitrarySolution nv =
  liftM (array (0,nv-1) . zip [0..]) $ replicateM nv arbitrary

instance (Arbitrary a, Eq a, Num a) => Arbitrary (QUBO.IsingModel a) where
  arbitrary = do
    nv <- choose (1,10)

    m <- choose (0,nv*nv)
    qq <- liftM (f . IntMap.unionsWith (IntMap.unionWith (+))) $ replicateM m $ do
      i <- choose (0,nv-1)
      j <- choose (i,nv-1)
      qq_ij <- arbitrary
      return $ IntMap.singleton i $ IntMap.singleton j qq_ij

    h <- liftM (\h -> IntMap.fromList [(i,hi)| (i, Just hi) <- zip [0..] h]) $ replicateM nv arbitrary

    return $
      QUBO.IsingModel
      { QUBO.isingNumVars = nv
      , QUBO.isingInteraction = qq
      , QUBO.isingExternalMagneticField = h
      }
    where
      f = IntMap.mapMaybe (g . IntMap.filter (/= 0))
      g m = if IntMap.null m then Nothing else Just m

------------------------------------------------------------------------

prop_qubo2pbo :: Property
prop_qubo2pbo = forAll arbitrary $ \qubo ->
  let (pbo,_) = qubo2pbo qubo
   in Just qubo === fmap fst (pboAsQUBO pbo)

prop_qubo2ising :: Property
prop_qubo2ising = forAll arbitrary $ \(qubo :: QUBO.Problem Integer) ->
  let (ising, info) = qubo2ising qubo
   in counterexample (show ising) $
        forAll (arbitrarySolution (QUBO.quboNumVars qubo)) $ \sol ->
          transformObjValueForward info (QUBO.eval sol qubo) === QUBO.evalIsingModel sol ising

prop_ising2qubo :: Property
prop_ising2qubo = forAll arbitrary $ \(ising :: QUBO.IsingModel Integer) ->
  let (qubo, info) = ising2qubo ising
   in counterexample (show qubo) $
        forAll (arbitrarySolution (QUBO.isingNumVars ising)) $ \sol ->
          transformObjValueForward info (QUBO.evalIsingModel sol ising) === QUBO.eval sol qubo

------------------------------------------------------------------------
-- Test harness

quboTestGroup :: TestTree
quboTestGroup = $(testGroupGenerator)
