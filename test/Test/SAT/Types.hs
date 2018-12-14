{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, FlexibleContexts #-}
module Test.SAT.Types (satTypesTestGroup) where

import Control.Applicative
import Control.Monad
import Data.Array.IArray
import Data.List

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH

import qualified ToySolver.SAT.Types as SAT

import Test.SAT.Utils

------------------------------------------------------------------------

-- -4*(not x1) + 3*x1 + 10*(not x2)
-- = -4*(1 - x1) + 3*x1 + 10*(not x2)
-- = -4 + 4*x1 + 3*x1 + 10*(not x2)
-- = 7*x1 + 10*(not x2) - 4
case_normalizePBLinSum_1 :: Assertion
case_normalizePBLinSum_1 = do
  sort e @?= sort [(7,x1),(10,-x2)]
  c @?= -4
  where
    x1 = 1
    x2 = 2
    (e,c) = SAT.normalizePBLinSum ([(-4,-x1),(3,x1),(10,-x2)], 0)

prop_normalizePBLinSum :: Property
prop_normalizePBLinSum = forAll g $ \(nv, (s,n)) ->
    let (s2,n2) = SAT.normalizePBLinSum (s,n)
    in flip all (allAssignments nv) $ \m ->
         SAT.evalPBLinSum m s + n == SAT.evalPBLinSum m s2 + n2
  where
    g :: Gen (Int, (SAT.PBLinSum, Integer))
    g = do
      nv <- choose (0, 10)
      s <- forM [1..nv] $ \x -> do
        c <- arbitrary
        p <- arbitrary
        return (c, SAT.literal x p)
      n <- arbitrary
      return (nv, (s,n))

-- -4*(not x1) + 3*x1 + 10*(not x2) >= 3
-- ⇔ -4*(1 - x1) + 3*x1 + 10*(not x2) >= 3
-- ⇔ -4 + 4*x1 + 3*x1 + 10*(not x2) >= 3
-- ⇔ 7*x1 + 10*(not x2) >= 7
-- ⇔ 7*x1 + 7*(not x2) >= 7
-- ⇔ x1 + (not x2) >= 1
case_normalizePBLinAtLeast_1 :: Assertion
case_normalizePBLinAtLeast_1 = (sort lhs, rhs) @?= (sort [(1,x1),(1,-x2)], 1)
  where
    x1 = 1
    x2 = 2
    (lhs,rhs) = SAT.normalizePBLinAtLeast ([(-4,-x1),(3,x1),(10,-x2)], 3)

prop_normalizePBLinAtLeast :: Property
prop_normalizePBLinAtLeast = forAll g $ \(nv, c) ->
    let c2 = SAT.normalizePBLinAtLeast c
    in flip all (allAssignments nv) $ \m ->
         SAT.evalPBLinAtLeast m c == SAT.evalPBLinAtLeast m c2
  where
    g :: Gen (Int, SAT.PBLinAtLeast)
    g = do
      nv <- choose (0, 10)
      lhs <- forM [1..nv] $ \x -> do
        c <- arbitrary
        p <- arbitrary
        return (c, SAT.literal x p)
      rhs <- arbitrary
      return (nv, (lhs,rhs))

case_normalizePBLinExactly_1 :: Assertion
case_normalizePBLinExactly_1 = (sort lhs, rhs) @?= ([], 1)
  where
    x1 = 1
    x2 = 2
    (lhs,rhs) = SAT.normalizePBLinExactly ([(6,x1),(4,x2)], 2)

case_normalizePBLinExactly_2 :: Assertion
case_normalizePBLinExactly_2 = (sort lhs, rhs) @?= ([], 1)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    (lhs,rhs) = SAT.normalizePBLinExactly ([(2,x1),(2,x2),(2,x3)], 3)

prop_normalizePBLinExactly :: Property
prop_normalizePBLinExactly = forAll g $ \(nv, c) ->
    let c2 = SAT.normalizePBLinExactly c
    in flip all (allAssignments nv) $ \m ->
         SAT.evalPBLinExactly m c == SAT.evalPBLinExactly m c2
  where
    g :: Gen (Int, SAT.PBLinExactly)
    g = do
      nv <- choose (0, 10)
      lhs <- forM [1..nv] $ \x -> do
        c <- arbitrary
        p <- arbitrary
        return (c, SAT.literal x p)
      rhs <- arbitrary
      return (nv, (lhs,rhs))

prop_cutResolve :: Property
prop_cutResolve =
  forAll (choose (1, 10)) $ \nv ->
    forAll (g nv True) $ \c1 ->
      forAll (g nv False) $ \c2 ->
        let c3 = SAT.cutResolve c1 c2 1
        in flip all (allAssignments nv) $ \m ->
             not (SAT.evalPBLinExactly m c1 && SAT.evalPBLinExactly m c2) || SAT.evalPBLinExactly m c3
  where
    g :: Int -> Bool -> Gen SAT.PBLinExactly
    g nv b = do
      lhs <- forM [1..nv] $ \x -> do
        if x==1 then do
          c <- liftM ((1+) . abs) arbitrary
          return (c, SAT.literal x b)
        else do
          c <- arbitrary
          p <- arbitrary
          return (c, SAT.literal x p)
      rhs <- arbitrary
      return (lhs, rhs)

case_cutResolve_1 :: Assertion
case_cutResolve_1 = (sort lhs, rhs) @?= (sort [(1,x3),(1,x4)], 1)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    x4 = 4
    pb1 = ([(1,x1), (1,x2), (1,x3)], 1)
    pb2 = ([(2,-x1), (2,-x2), (1,x4)], 3)
    (lhs,rhs) = SAT.cutResolve pb1 pb2 x1

case_cutResolve_2 :: Assertion
case_cutResolve_2 = (sort lhs, rhs) @?= (sort lhs2, rhs2)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    x4 = 4
    pb1 = ([(3,x1), (2,-x2), (1,x3), (1,x4)], 3)
    pb2 = ([(1,-x3), (1,x4)], 1)
    (lhs,rhs) = SAT.cutResolve pb1 pb2 x3
    (lhs2,rhs2) = ([(2,x1),(1,-x2),(1,x4)],2) -- ([(3,x1),(2,-x2),(2,x4)], 3)

case_cardinalityReduction :: Assertion
case_cardinalityReduction = (sort lhs, rhs) @?= ([1,2,3,4,5],4)
  where
    (lhs, rhs) = SAT.cardinalityReduction ([(6,1),(5,2),(4,3),(3,4),(2,5),(1,6)], 17)

case_pbSubsume_clause :: Assertion
case_pbSubsume_clause = SAT.pbSubsume ([(1,1),(1,-3)],1) ([(1,1),(1,2),(1,-3),(1,4)],1) @?= True

case_pbSubsume_1 :: Assertion
case_pbSubsume_1 = SAT.pbSubsume ([(1,1),(1,2),(1,-3)],2) ([(1,1),(2,2),(1,-3),(1,4)],1) @?= True

case_pbSubsume_2 :: Assertion
case_pbSubsume_2 = SAT.pbSubsume ([(1,1),(1,2),(1,-3)],2) ([(1,1),(2,2),(1,-3),(1,4)],3) @?= False

prop_removeNegationFromPBSum :: Property
prop_removeNegationFromPBSum =
  forAll (choose (0,10)) $ \nv ->
    forAll (arbitraryPBSum nv) $ \s ->
      let s' = SAT.removeNegationFromPBSum s
       in counterexample (show s') $ 
            forAll (arbitraryAssignment nv) $ \m -> SAT.evalPBSum m s === SAT.evalPBSum m s'

------------------------------------------------------------------------

case_normalizeXORClause_False :: Assertion
case_normalizeXORClause_False =
  SAT.normalizeXORClause ([],True) @?= ([],True)

case_normalizeXORClause_True :: Assertion
case_normalizeXORClause_True =
  SAT.normalizeXORClause ([],False) @?= ([],False)

-- x ⊕ y ⊕ x = y
case_normalizeXORClause_case1 :: Assertion
case_normalizeXORClause_case1 =
  SAT.normalizeXORClause ([1,2,1],True) @?= ([2],True)

-- x ⊕ ¬x = x ⊕ x ⊕ 1 = 1
case_normalizeXORClause_case2 :: Assertion
case_normalizeXORClause_case2 =
  SAT.normalizeXORClause ([1,-1],True) @?= ([],False)

prop_normalizeXORClause :: Property
prop_normalizeXORClause = forAll g $ \(nv, c) ->
    let c2 = SAT.normalizeXORClause c
    in flip all (allAssignments nv) $ \m ->
         SAT.evalXORClause m c == SAT.evalXORClause m c2
  where
    g :: Gen (Int, SAT.XORClause)
    g = do
      nv <- choose (0, 10)
      len <- choose (0, nv)
      lhs <- replicateM len $ choose (-nv, nv) `suchThat` (/= 0)
      rhs <- arbitrary
      return (nv, (lhs,rhs))

case_evalXORClause_case1 :: Assertion
case_evalXORClause_case1 =
  SAT.evalXORClause (array (1,2) [(1,True),(2,True)] :: Array Int Bool) ([1,2], True) @?= False

case_evalXORClause_case2 :: Assertion
case_evalXORClause_case2 =
  SAT.evalXORClause (array (1,2) [(1,False),(2,True)] :: Array Int Bool) ([1,2], True) @?= True

------------------------------------------------------------------------

satTypesTestGroup :: TestTree
satTypesTestGroup = $(testGroupGenerator)
