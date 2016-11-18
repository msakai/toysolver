{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Test.HittingSets (hittingSetsTestGroup) where

import Prelude hiding (all)

import Control.Arrow
import Control.Monad
import Data.Foldable (all)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Ratio
import Data.Set (Set)
import qualified Data.Set as Set
import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified ToySolver.Combinatorial.HittingSet.Simple as HittingSet
import qualified ToySolver.Combinatorial.HittingSet.FredmanKhachiyan1996 as FredmanKhachiyan1996
import qualified ToySolver.Combinatorial.HittingSet.GurvichKhachiyan1999 as GurvichKhachiyan1999
import qualified ToySolver.Combinatorial.HittingSet.DAA as DAA

-- ---------------------------------------------------------------------
-- Hitting sets

case_minimalHittingSets_1 :: Assertion
case_minimalHittingSets_1 = actual @?= expected
  where
    actual    = HittingSet.minimalHittingSets $ Set.fromList $ map IntSet.fromList [[1], [2,3,5], [2,3,6], [2,4,5], [2,4,6]]
    expected  = Set.fromList $ map IntSet.fromList [[1,2], [1,3,4], [1,5,6]]

-- an example from http://kuma-san.net/htcbdd.html
case_minimalHittingSets_2 :: Assertion
case_minimalHittingSets_2 = actual @?= expected
  where
    actual    = HittingSet.minimalHittingSets $ Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9], [9,10]]
    expected  = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9]]

hyperGraph :: Gen (Set IntSet)
hyperGraph = do
  nv <- choose (0, 10)
  ne <- if nv==0 then return 0 else choose (0, 20)
  liftM Set.fromList $ replicateM ne $ do
    n <- choose (1,nv)
    liftM IntSet.fromList $ replicateM n $ choose (1, nv)

isHittingSetOf :: IntSet -> Set IntSet -> Bool
isHittingSetOf s g = all (\e -> not (IntSet.null (s `IntSet.intersection` e))) g

prop_minimalHittingSets_duality :: Property
prop_minimalHittingSets_duality =
  forAll hyperGraph $ \g ->
    let h = HittingSet.minimalHittingSets g
    in h == HittingSet.minimalHittingSets (HittingSet.minimalHittingSets h)

prop_minimalHittingSets_isHittingSet :: Property
prop_minimalHittingSets_isHittingSet =
  forAll hyperGraph $ \g ->
    all (`isHittingSetOf` g) (HittingSet.minimalHittingSets g)

prop_minimalHittingSets_minimality :: Property
prop_minimalHittingSets_minimality =
  forAll hyperGraph $ \g ->
    forAll (elements (Set.toList (HittingSet.minimalHittingSets g))) $ \s ->
      if IntSet.null s then
        property True
      else
        forAll (elements (IntSet.toList s)) $ \v ->
          not $ IntSet.delete v s `isHittingSetOf` g

mutuallyDualHypergraphs :: Gen (Set IntSet, Set IntSet)
mutuallyDualHypergraphs = do
  g <- liftM HittingSet.minimalHittingSets hyperGraph
  let f = HittingSet.minimalHittingSets g
  return (f,g)

mutuallyDualDNFs :: Gen (Set IntSet, Set IntSet)
mutuallyDualDNFs = do
  (f,g) <- mutuallyDualHypergraphs
  let xs = IntSet.unions $ Set.toList $ f `Set.union` g
  if IntSet.null xs then
    return (f,g)
  else do
    let xs' = IntSet.toList xs
    let mutate h = liftM Set.unions $ do
          forM (Set.toList h) $ \is -> oneof $
            [ return $ Set.singleton is
            , do i <- elements xs'
                 return $ Set.fromList [is, IntSet.insert i is]
            ]
    f' <- mutate f
    g' <- mutate g
    return (f',g')

-- Pair of DNFs that are nearly dual.
pairOfDNFs :: Gen (Set IntSet, Set IntSet)
pairOfDNFs = do
  (f,g) <- mutuallyDualDNFs
  let mutate h = liftM Set.unions $ do
        forM (Set.toList h) $ \is -> oneof $
          [return Set.empty, return (Set.singleton is)] ++
          [ do x <- elements (IntSet.toList is)
               return $ Set.singleton $ IntSet.delete x is
          | not (IntSet.null is)
          ]
  return (f,g)

prop_FredmanKhachiyan1996_checkDualityA_prop1 :: Property
prop_FredmanKhachiyan1996_checkDualityA_prop1 =
  forAll mutuallyDualDNFs $ \(f,g) ->
    FredmanKhachiyan1996.checkDualityA f g == Nothing

prop_FredmanKhachiyan1996_checkDualityA_prop2 :: Property
prop_FredmanKhachiyan1996_checkDualityA_prop2 =
  forAll pairOfDNFs $ \(f,g) ->
    case FredmanKhachiyan1996.checkDualityA f g of
      Nothing -> True
      Just xs -> xs `FredmanKhachiyan1996.isCounterExampleOf` (f,g)

prop_FredmanKhachiyan1996_checkDualityB_prop1 :: Property
prop_FredmanKhachiyan1996_checkDualityB_prop1 =
  forAll mutuallyDualDNFs $ \(f,g) ->
    FredmanKhachiyan1996.checkDualityA f g == Nothing

prop_FredmanKhachiyan1996_checkDualityB_prop2 :: Property
prop_FredmanKhachiyan1996_checkDualityB_prop2 =
  forAll pairOfDNFs $ \(f,g) ->
    case FredmanKhachiyan1996.checkDualityB f g of
      Nothing -> True
      Just xs -> xs `FredmanKhachiyan1996.isCounterExampleOf` (f,g)

prop_FredmanKhachiyan1996_lemma_1 :: Property
prop_FredmanKhachiyan1996_lemma_1 =
  forAll mutuallyDualHypergraphs $ \(f,g) ->
    let e :: Rational
        e = sum [1 % (2 ^ IntSet.size i) | i <- Set.toList f] +
            sum [1 % (2 ^ IntSet.size j) | j <- Set.toList g]
    in e >= 1

prop_FredmanKhachiyan1996_corollary_1 :: Property
prop_FredmanKhachiyan1996_corollary_1 =
  forAll mutuallyDualHypergraphs $ \(f,g) ->
    let n = Set.size f + Set.size g
        m = minimum [IntSet.size is | is <- Set.toList (f `Set.union` g)]
    in (fromIntegral m :: Double) <= logBase 2 (fromIntegral n)

prop_FredmanKhachiyan1996_lemma_2 :: Property
prop_FredmanKhachiyan1996_lemma_2 =
  forAll mutuallyDualHypergraphs $ \(f,g) ->
    let n = Set.size f + Set.size g
        epsilon :: Double
        epsilon = 1 / logBase 2 (fromIntegral n)
        vs = IntSet.unions $ Set.toList $ f `Set.union` g
    in (Set.size f * Set.size g >= 1)
       ==> any (\v -> FredmanKhachiyan1996.occurFreq v f >= epsilon || FredmanKhachiyan1996.occurFreq v g >= epsilon) (IntSet.toList vs)

prop_FredmanKhachiyan1996_lemma_3_a :: Property
prop_FredmanKhachiyan1996_lemma_3_a =
  forAll mutuallyDualHypergraphs $ \(f,g) ->
    let vs = IntSet.unions $ Set.toList $ f `Set.union` g
        x = IntSet.findMin vs
        -- f = x f0 ∨ f1
        (f0, f1) = Set.map (IntSet.delete x) *** id $ Set.partition (x `IntSet.member`) f
        -- g = x g0 ∨ g1
        (g0, g1) = Set.map (IntSet.delete x) *** id $ Set.partition (x `IntSet.member`) g
    in not (IntSet.null vs)
       ==>
         HittingSet.minimalHittingSets f1 == FredmanKhachiyan1996.deleteRedundancy (g0 `Set.union` g1) &&
         HittingSet.minimalHittingSets g1 == FredmanKhachiyan1996.deleteRedundancy (f0 `Set.union` f1)

prop_FredmanKhachiyan1996_to_selfDuality :: Property
prop_FredmanKhachiyan1996_to_selfDuality =
  forAll mutuallyDualHypergraphs $ \(f,g) ->
    let vs = IntSet.unions $ Set.toList $ f `Set.union` g
        y = if IntSet.null vs then 0 else IntSet.findMax vs + 1
        z = y + 1
        h = FredmanKhachiyan1996.deleteRedundancy $ Set.unions
              [ Set.map (IntSet.insert y) f
              , Set.map (IntSet.insert z) g
              , Set.singleton (IntSet.fromList [y,z])
              ] 
    in HittingSet.minimalHittingSets h == h

case_FredmanKhachiyan1996_condition_1_1_solve_L :: Assertion
case_FredmanKhachiyan1996_condition_1_1_solve_L = (xs `FredmanKhachiyan1996.isCounterExampleOf` (f,g)) @?= True
  where
    Just xs = FredmanKhachiyan1996.condition_1_1_solve f g
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9], [4]]
    g = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9]]

case_FredmanKhachiyan1996_condition_1_1_solve_R :: Assertion
case_FredmanKhachiyan1996_condition_1_1_solve_R = (xs `FredmanKhachiyan1996.isCounterExampleOf` (f,g)) @?= True
  where
    Just xs = FredmanKhachiyan1996.condition_1_1_solve f g
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9]]
    g = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9], [4,7,8]]

case_FredmanKhachiyan1996_condition_1_2_solve_L :: Assertion
case_FredmanKhachiyan1996_condition_1_2_solve_L = (xs `FredmanKhachiyan1996.isCounterExampleOf` (f,g)) @?= True
  where
    Just xs = FredmanKhachiyan1996.condition_1_2_solve f g
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9,10]]
    g = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9]]

case_FredmanKhachiyan1996_condition_1_2_solve_R :: Assertion
case_FredmanKhachiyan1996_condition_1_2_solve_R = (xs `FredmanKhachiyan1996.isCounterExampleOf` (f,g)) @?= True
  where
    Just xs = FredmanKhachiyan1996.condition_1_2_solve f g
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9]]
    g = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9,10]]

case_FredmanKhachiyan1996_condition_1_3_solve_L :: Assertion
case_FredmanKhachiyan1996_condition_1_3_solve_L = (xs `FredmanKhachiyan1996.isCounterExampleOf` (f,g)) @?= True
  where
    Just xs = FredmanKhachiyan1996.condition_1_3_solve f g
    f = Set.fromList $ map IntSet.fromList [[2,4,7,10], [7,8], [9]]
    g = Set.fromList $ map IntSet.fromList [[7,9,10], [4,8,9], [2,8,9]]

case_FredmanKhachiyan1996_condition_1_3_solve_R :: Assertion
case_FredmanKhachiyan1996_condition_1_3_solve_R = (xs `FredmanKhachiyan1996.isCounterExampleOf` (f,g)) @?= True
  where
    Just xs = FredmanKhachiyan1996.condition_1_3_solve f g
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9,10]]
    g = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9,10]]

case_FredmanKhachiyan1996_condition_2_1_solve_L :: Assertion
case_FredmanKhachiyan1996_condition_2_1_solve_L = (xs `FredmanKhachiyan1996.isCounterExampleOf` (f,g)) @?= True
  where
    Just xs = FredmanKhachiyan1996.condition_2_1_solve f g
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [4,7,9], [7,8,9]]
    g = Set.fromList $ map IntSet.fromList [[2,4,7], [2,8,9], [4,8,9]]

case_FredmanKhachiyan1996_condition_2_1_solve_R :: Assertion
case_FredmanKhachiyan1996_condition_2_1_solve_R = (xs `FredmanKhachiyan1996.isCounterExampleOf` (f,g)) @?= True
  where
    Just xs = FredmanKhachiyan1996.condition_2_1_solve f g
    g = Set.fromList $ map IntSet.fromList [[2,4,7], [4,7,9], [7,8,9]]
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [2,8,9], [4,8,9]]

case_FredmanKhachiyan1996_checkDualityA :: Assertion
case_FredmanKhachiyan1996_checkDualityA = FredmanKhachiyan1996.checkDualityA f g @?= Nothing
  where
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9]]
    g = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9]]

case_FredmanKhachiyan1996_checkDualityB :: Assertion
case_FredmanKhachiyan1996_checkDualityB = FredmanKhachiyan1996.checkDualityB f g @?= Nothing
  where
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9]]
    g = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9]]

prop_GurvichKhachiyan1999_generateCNFAndDNF :: Property
prop_GurvichKhachiyan1999_generateCNFAndDNF =
  forAll hyperGraph $ \g ->
    let vs = IntSet.unions $ Set.toList g
        f xs = any (\is -> not $ IntSet.null $ xs `IntSet.intersection` is) (Set.toList g)
        dual f is = not $ f (vs `IntSet.difference` is)
        is `isImplicantOf` f = f is
        is `isImplicateOf` f = is `isImplicantOf` dual f
        is `isPrimeImplicantOf` f = is `isImplicantOf` f && all (\i -> not (IntSet.delete i is `isImplicantOf` f)) (IntSet.toList is)
        is `isPrimeImplicateOf` f = is `isImplicateOf` f && all (\i -> not (IntSet.delete i is `isImplicateOf` f)) (IntSet.toList is)
        (cnf,dnf) = GurvichKhachiyan1999.generateCNFAndDNF vs f Set.empty Set.empty
    in all (`isPrimeImplicantOf` f) (Set.toList dnf) &&
       all (`isPrimeImplicateOf` f) (Set.toList cnf)

prop_GurvichKhachiyan1999_minimalHittingSets_duality :: Property
prop_GurvichKhachiyan1999_minimalHittingSets_duality =
  forAll hyperGraph $ \g ->
    let h = GurvichKhachiyan1999.minimalHittingSets g
    in h == GurvichKhachiyan1999.minimalHittingSets (GurvichKhachiyan1999.minimalHittingSets h)

prop_GurvichKhachiyan1999_minimalHittingSets_isHittingSet :: Property
prop_GurvichKhachiyan1999_minimalHittingSets_isHittingSet =
  forAll hyperGraph $ \g ->
    all (`isHittingSetOf` g) (GurvichKhachiyan1999.minimalHittingSets g)

prop_GurvichKhachiyan1999_minimalHittingSets_minimality :: Property
prop_GurvichKhachiyan1999_minimalHittingSets_minimality =
  forAll hyperGraph $ \g ->
    forAll (elements (Set.toList (GurvichKhachiyan1999.minimalHittingSets g))) $ \s ->
      if IntSet.null s then
        property True
      else
        forAll (elements (IntSet.toList s)) $ \v ->
          not $ IntSet.delete v s `isHittingSetOf` g

prop_DAA_generateCNFAndDNF :: Property
prop_DAA_generateCNFAndDNF =
  forAll hyperGraph $ \g ->
    let vs = IntSet.unions $ Set.toList g
        f xs = any (\is -> not $ IntSet.null $ xs `IntSet.intersection` is) (Set.toList g)
        dual f is = not $ f (vs `IntSet.difference` is)
        is `isImplicantOf` f = f is
        is `isImplicateOf` f = is `isImplicantOf` dual f
        is `isPrimeImplicantOf` f = is `isImplicantOf` f && all (\i -> not (IntSet.delete i is `isImplicantOf` f)) (IntSet.toList is)
        is `isPrimeImplicateOf` f = is `isImplicateOf` f && all (\i -> not (IntSet.delete i is `isImplicateOf` f)) (IntSet.toList is)
        (cnf,dnf) = DAA.generateCNFAndDNF vs f
    in all (`isPrimeImplicantOf` f) (Set.toList dnf) &&
       all (`isPrimeImplicateOf` f) (Set.toList cnf)

------------------------------------------------------------------------
-- Test harness

hittingSetsTestGroup :: TestTree
hittingSetsTestGroup = $(testGroupGenerator)
