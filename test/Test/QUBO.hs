{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, FlexibleContexts #-}
module Test.QUBO (quboTestGroup) where

import Control.Monad
import Data.Array.IArray
import Data.ByteString.Builder
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe
import qualified Data.PseudoBoolean as PBFile
import Data.Scientific

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import ToySolver.Converter
import qualified ToySolver.FileFormat as FF
import qualified ToySolver.QUBO as QUBO
import ToySolver.Converter.QUBO
import qualified ToySolver.SAT.Types as SAT

import Test.SAT.Utils

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

prop_QUBO_ReadWrite_Invariance :: Property
prop_QUBO_ReadWrite_Invariance = forAll g $ \qubo ->
  let s = toLazyByteString (FF.render qubo)
   in counterexample (show s) $ FF.parse s === Right qubo
  where
    g = do
      qubo <- arbitrary
      return $ fmap fromFloatDigits (qubo :: QUBO.Problem Double)

------------------------------------------------------------------------

prop_qubo2pbo :: Property
prop_qubo2pbo = forAll arbitrary $ \qubo ->
  let (pbo,_) = qubo2pbo qubo
   in Just qubo === fmap fst (pboAsQUBO pbo)

prop_pb2qubo :: Property
prop_pb2qubo = forAll arbitraryPBFormula $ \formula ->
  let ((qubo,th), info) = pb2qubo formula
   in counterexample (show (qubo,th,info)) $
        conjoin
        [ forAll (arbitraryAssignment (PBFile.pbNumVars formula)) $ \m ->
            case SAT.evalPBFormula m formula of
              Nothing ->
                property (QUBO.eval (transformForward info m) qubo > th)
              Just o ->
                conjoin
                [ QUBO.eval (transformForward info m) qubo === transformObjValueForward info o
                , transformObjValueBackward info (transformObjValueForward info o) === o
                , property (transformObjValueForward info o <= th)
                ]
        , forAll (arbitrarySolution (QUBO.quboNumVars qubo)) $ \sol ->
            let o = QUBO.eval sol qubo
             in if (o <= th) then
                  (SAT.evalPBFormula (transformBackward info sol) formula === Just (transformObjValueBackward info o))
                  .&&.
                  transformObjValueForward info (transformObjValueBackward info o) === o
                else
                  property True
        ]

prop_qubo2ising :: Property
prop_qubo2ising = forAll arbitrary $ \(qubo :: QUBO.Problem Rational) ->
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
