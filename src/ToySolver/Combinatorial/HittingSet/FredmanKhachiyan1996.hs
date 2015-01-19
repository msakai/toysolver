{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Combinatorial.HittingSet.FredmanKhachiyan1996
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- This modules provides functions to check whether two monotone boolean
-- functions /f/ and /g/ given in DNFs are mutually dual (/i.e./ f(x1,…,xn) = ¬g(¬x1,…,¬xn)).
--
-- References:
--
-- * [FredmanKhachiyan1996] Michael L. Fredman and Leonid Khachiyan,
--   On the Complexicy of Dualization of Monotone Disjunctifve Normal Forms,
--   Journal of Algorithms, vol. 21, pp. 618-628, 1996.
--   <http://www.sciencedirect.com/science/article/pii/S0196677496900620>
--   <http://www.cs.tau.ac.il/~fiat/dmsem03/On%20the%20complexity%20of%20Dualization%20of%20monotone%20Disjunctive%20Normal%20Forms%20-%201996.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.Combinatorial.HittingSet.FredmanKhachiyan1996
  (
  -- * Main functions
    areDualDNFs
  , checkDuality
  , checkDualityA
  , checkDualityB

  -- * Redundancy
  -- $Redundancy
  , isRedundant
  , deleteRedundancy

  -- * Utilities for testing
  , isCounterExampleOf
  , occurFreq
  ) where

import Prelude hiding (all, any)
import Control.Arrow ((***))
import Control.Exception (assert)
import Control.Monad
import Data.Foldable (all, any)
import Data.Function
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List hiding (all, any, intersect)
import Data.Maybe
import Data.Ratio
import Data.Set (Set)
import qualified Data.Set as Set

-- | xhi n ** xhi n == n
xhi :: Double -> Double
xhi n = iterate f m !! 30
  where
    m = logn / logBase 2 logn
      where
        logn = logBase 2 n
    f x = m * ((logx + logBase 2 logx) / logx)
      where
        logx = logBase 2 x

disjoint :: IntSet -> IntSet -> Bool
disjoint xs ys = IntSet.null $ xs `IntSet.intersection` ys

intersect :: IntSet -> IntSet -> Bool
intersect xs ys = not $ disjoint xs ys

isHittingSetOf :: IntSet -> Set IntSet -> Bool
isHittingSetOf xs yss = all (xs `intersect`) yss

isCounterExampleOf :: IntSet -> (Set IntSet, Set IntSet) -> Bool
isCounterExampleOf xs (f,g) = lhs == rhs
  where
    lhs = or [is `IntSet.isSubsetOf` xs | is <- Set.toList f]
    rhs = or [xs `disjoint` js | js <- Set.toList g]

volume :: Set IntSet -> Set IntSet -> Int
volume f g = Set.size f * Set.size g

condition_1_1 :: Set IntSet -> Set IntSet -> Bool
condition_1_1 f g = all (\is -> all (\js -> is `intersect` js) g) f

condition_1_1_solve :: Set IntSet -> Set IntSet -> Maybe IntSet
condition_1_1_solve f g = listToMaybe $ do
  is <- Set.toList f
  js <- Set.toList g
  guard $ is `disjoint` js
  return is

condition_1_2 :: Set IntSet -> Set IntSet -> Bool
condition_1_2 f g = h f == h g
  where
    h = IntSet.unions . Set.toList

-- | Find @xs@ such that @xs `isCounterExampleOf` (f,g)@ unless @'condition_1_2' f g@.
condition_1_2_solve :: Set IntSet -> Set IntSet -> Maybe IntSet
condition_1_2_solve f g
  | Just (v1,_) <- IntSet.minView d1 = Just $ head [IntSet.delete v1 is | is <- Set.toList f, v1 `IntSet.member` is]
  | Just (v2,_) <- IntSet.minView d2 = Just $ head [(vs `IntSet.difference` (IntSet.delete v2 js)) | js <- Set.toList g, v2 `IntSet.member` js]
  | otherwise = Nothing
  where
    f_vs = IntSet.unions $ Set.toList f
    g_vs = IntSet.unions $ Set.toList g
    vs = f_vs `IntSet.union` g_vs
    d1 = f_vs `IntSet.difference` g_vs
    d2 = g_vs `IntSet.difference` f_vs

condition_1_3 :: Set IntSet -> Set IntSet -> Bool
condition_1_3 f g = maxSize f <= Set.size g && maxSize g <= Set.size f
  where
    maxSize xs = foldl' max 0 [IntSet.size i | i <- Set.toList xs]

condition_1_3_solve :: Set IntSet -> Set IntSet -> Maybe IntSet
condition_1_3_solve f g = listToMaybe $
  [head [is' | i <- IntSet.toList is, let is' = IntSet.delete i is, is' `isHittingSetOf` g] | is <- Set.toList f, IntSet.size is > g_size] ++
  [xs `IntSet.difference` head [js' | j <- IntSet.toList js, let js' = IntSet.delete j js, js' `isHittingSetOf` f] | js <- Set.toList g, IntSet.size js > f_size]
  where
    xs = IntSet.unions $ Set.toList $ Set.union f g
    f_size = Set.size f
    g_size = Set.size g

e :: Set IntSet -> Set IntSet -> Rational
e f g = sum [1 % (2 ^ IntSet.size i) | i <- Set.toList f] +
        sum [1 % (2 ^ IntSet.size j) | j <- Set.toList g]

condition_2_1 :: Set IntSet -> Set IntSet -> Bool
condition_2_1 f g = e f g >= 1

condition_2_1_solve :: Set IntSet -> Set IntSet -> Maybe IntSet
condition_2_1_solve f g =
  if condition_2_1 f g
  then Nothing
  else Just $ loop (IntSet.toList vs) f g IntSet.empty
  where
    vs = IntSet.unions $ Set.toList $ Set.union f g

    loop :: [Int] -> Set IntSet -> Set IntSet -> IntSet -> IntSet
    loop [] _ _ ret = ret
    loop (v:vs) f g ret =
      if e f1 g1 <= e f2 g2
      then loop vs f1 g1 (IntSet.insert v ret)
      else loop vs f2 g2 ret
      where
        -- f = x f1 ∨ f2
        -- g = x g2 ∨ g1
        f1 = Set.map (IntSet.delete v) f
        g1 = Set.filter (v `IntSet.notMember`) g
        f2 = Set.filter (v `IntSet.notMember`) f
        g2 = Set.map (IntSet.delete v) g

-- | @'isRedundant' F@ tests whether /F/ contains redundant implicants.
isRedundant :: Set IntSet -> Bool
isRedundant = loop . sortBy (compare `on` IntSet.size) . Set.toList
  where
    loop :: [IntSet] -> Bool
    loop [] = False
    loop (xs:yss) = or [xs `IntSet.isSubsetOf` ys | ys <- yss] || loop yss

isIrredundant :: Set IntSet -> Bool
isIrredundant = not . isRedundant

-- | Removes redundant implicants from a given DNF.
deleteRedundancy :: Set IntSet -> Set IntSet
deleteRedundancy = foldl' f Set.empty . sortBy (compare `on` IntSet.size) . Set.toList
  where
    f :: Set IntSet -> IntSet -> Set IntSet
    f xss ys =
      if any (`IntSet.isSubsetOf` ys) xss
      then xss
      else Set.insert ys xss

-- | @occurFreq  x F@ computes /|{I∈F | x∈I}| \/ |F|/
occurFreq
  :: Fractional a
  => Int -- ^ a variable /x/
  -> Set IntSet -- ^ a DNF /F/
  -> a
occurFreq x f = fromIntegral (sum [1 | is <- Set.toList f, x `IntSet.member` is] :: Int) / fromIntegral (Set.size f)

-- | @areDualDNFs f g@ checks whether two monotone boolean functions /f/
-- and /g/ are mutually dual (/i.e./ f(x1,…,xn) = ¬g(¬x1,…,xn)).
--
-- Note that this function does not care about redundancy of DNFs.
--
-- Complexity: /O(n^o(log n))/ where @n = 'IntSet.size' f + 'IntSet.size' g@.
areDualDNFs
  :: Set IntSet -- ^ a monotone boolean function /f/ given in DNF
  -> Set IntSet -- ^ a monotone boolean function /g/ given in DNF
  -> Bool
areDualDNFs f g = isNothing $ checkDualityB f g

-- | Synonym for 'checkDualityB'.
checkDuality :: Set IntSet -> Set IntSet -> Maybe IntSet
checkDuality = checkDualityB

-- | @checkDualityA f g@ checks whether two monotone boolean functions /f/
-- and /g/ are mutually dual (/i.e./ f(x1,…,xn) = ¬g(¬x1,…,¬xn)) using
-- “Algorithm A” of [FredmanKhachiyan1996].
--
-- If they are indeed mutually dual it returns @Nothing@, otherwise
-- it returns @Just cs@ such that {xi ↦ (if xi∈cs then True else False) | i∈{1…n}}
-- is a solution of f(x1,…,xn) = g(¬x1,…,¬xn)).
--
-- Note that this function does not care about redundancy of DNFs.
--
-- Complexity: /O(n^O(log^2 n))/ where @n = 'IntSet.size' f + 'IntSet.size' g@.
checkDualityA
  :: Set IntSet -- ^ a monotone boolean function /f/ given in DNF
  -> Set IntSet -- ^ a monotone boolean function /g/ given in DNF
  -> Maybe IntSet
checkDualityA f g
  | Just xs <- condition_1_1_solve f g = Just xs
  | otherwise = checkDualityA' (deleteRedundancy f) (deleteRedundancy g)

checkDualityA' :: Set IntSet -> Set IntSet -> Maybe IntSet
checkDualityA' f g
  | assert (isIrredundant f && isIrredundant g) False = undefined
  | Just s <- condition_1_2_solve f g = Just s
  | Just s <- condition_1_3_solve f g = Just s
  | Just s <- condition_2_1_solve f g = Just s
  | v <= 1 = solveSmall f g
  | otherwise = msum
      [ -- If x=0 then f(xs)=g(¬xs) ⇔ f1(xs) = g0(¬xs) ∨ g1(¬xs)
        checkDualityA' f1 (deleteRedundancy (g0 `Set.union` g1))
      , -- If x=1 then f(xs)=g(¬xs) ⇔ f0(xs) ∨ f1(xs) = g1(¬xs)
        liftM (IntSet.insert x) $ checkDualityA' (deleteRedundancy (f0 `Set.union` f1)) g1
      ]
  where
    size_f = Set.size f
    size_g = Set.size g
    n = size_f + size_g
    v = size_f * size_g
    xs = IntSet.unions $ Set.toList $ f `Set.union` g
    epsilon :: Double
    epsilon = 1 / logBase 2 (fromIntegral n)
    x = head [x | x <- IntSet.toList xs, occurFreq x f >= epsilon || occurFreq x g >= epsilon]
    -- f = x f0 ∨ f1
    (f0, f1) = Set.map (IntSet.delete x) *** id $ Set.partition (x `IntSet.member`) f
    -- g = x g0 ∨ g1
    (g0, g1) = Set.map (IntSet.delete x) *** id $ Set.partition (x `IntSet.member`) g

solveSmall :: Set IntSet -> Set IntSet -> Maybe IntSet
solveSmall f g
  | assert (isIrredundant f && isIrredundant g) False = undefined
  | Set.null f && Set.null g = Just IntSet.empty
  | Set.null f = assert (not (Set.null g)) $
      if IntSet.empty `Set.member` g
      then Nothing
      else Just (IntSet.unions (Set.toList g))
  | Set.null g = assert (not (Set.null f)) $
      if IntSet.empty `Set.member` f
      then Nothing
      else Just IntSet.empty
  | size_f == 1 && size_g == 1 =
      let
        is = Set.findMin f
        js = Set.findMin g
        is_size = IntSet.size is
        js_size = IntSet.size js
      in if is_size == 1 then
           if js_size == 1 then
             Nothing
           else
             Just (js `IntSet.difference` is)
         else
           Just (is `IntSet.difference` js)
  | otherwise = error "should not happen"
  where
    size_f = Set.size f
    size_g = Set.size g

-- | @checkDualityB f g@ checks whether two monotone boolean functions /f/
-- and /g/ are mutually dual (i.e. f(x1,…,xn) = ¬g(¬x1,…,xn)) using
-- “Algorithm B” of [FredmanKhachiyan1996].
--
-- If they are indeed mutually dual it returns @Nothing@, otherwise
-- it returns @Just cs@ such that {xi ↦ (if xi∈cs then True else False) | i∈{1…n}}
-- is a solution of f(x1,…,xn) = g(¬x1,…,xn)).
-- 
-- Note that this function does not care about redundancy of DNFs.
--
-- Complexity: /O(n^o(log n))/ where @n = 'Set.size' f + 'Set.size' g@.
checkDualityB
  :: Set IntSet -- ^ a monotone boolean function /f/ given in DNF
  -> Set IntSet -- ^ a monotone boolean function /f/ given in DNF
  -> Maybe IntSet
checkDualityB f g
  | Just xs <- condition_1_1_solve f g = Just xs
  | otherwise = checkDualityB' (deleteRedundancy f) (deleteRedundancy g)

checkDualityB' :: Set IntSet -> Set IntSet -> Maybe IntSet
checkDualityB' f g
  | assert (isIrredundant f && isIrredundant g) False = undefined
  | Just s <- condition_1_2_solve f g = Just s
  | Just s <- condition_1_3_solve f g = Just s
  | Just s <- condition_2_1_solve f g = Just s
  | v <= 1 = solveSmall f g
--  | min size_f size_g <= 2 = undefined
  | otherwise =
      let x = head [x | x <- IntSet.toList xs, occurFreq x f > (0::Rational), occurFreq x g > (0::Rational)]
          -- f = x f0 ∨ f1
          (f0, f1) = Set.map (IntSet.delete x) *** id $ Set.partition (x `IntSet.member`) f
          -- g = x g0 ∨ g1
          (g0, g1) = Set.map (IntSet.delete x) *** id $ Set.partition (x `IntSet.member`) g
          epsilon_x_f :: Double
          epsilon_x_f = occurFreq x f
          epsilon_x_g :: Double
          epsilon_x_g = occurFreq x g
      in if epsilon_x_f <= epsilon_v then
           msum
           [ {- If x=0 then f(xs)=g(¬xs) ⇔ f1(xs) = g0(¬xs) ∨ g1(¬xs). -}
             checkDualityB' f1 (deleteRedundancy (g0 `Set.union` g1))
           , {- If x=1 then f(xs)=g(¬xs) ⇔ f0(xs) ∨ f1(xs) = g1(¬xs).
                f(¬xs)=g(xs)
                ⇔ f0(¬xs) ∨ f1(¬xs) = g1(xs)  {- assuming x=1 -}
                ⇔ f0(¬xs) ∨ (¬g0(xs)∧¬g1(xs)) = g1(xs) {- duality of f1 and g0∨g1 -}
                ⇔ f0(¬xs) = g1(xs) and g0(xs) = 1
                   {- g0(xs)=0 is impossible, because
                      it implies f0(¬xs)∨¬g1(xs)=g1(xs) and then
                      f0(¬xs)=g1(xs)=1 which contradicts condition (1.1) -}
              -}
             liftM (xs `IntSet.difference`) $ msum $ do
               js <- Set.toList g0
               let f' = Set.filter (js `disjoint`) f0
                   g' = Set.map (`IntSet.difference` js) g1
               return $ checkDualityB' (deleteRedundancy g') (deleteRedundancy f')
           ]
         else if epsilon_x_g <= epsilon_v then
           msum
           [ {- If x=1 then f(xs)=g(¬xs) ⇔ f0(xs) ∨ f1(xs) = g1(¬xs). -}
             liftM (IntSet.insert x) $ checkDualityB' (deleteRedundancy (f0 `Set.union` f1)) g1
           , {- If x=0 then f(xs)=g(¬xs) ⇔ f1(xs) = g0(¬xs) ∨ g1(¬xs).
                f(xs)=g(¬xs)
                ⇔ f1(¬xs) = g0(xs) ∨ g1(xs)  {- assuming x=0 -}
                ⇔ f1(¬xs) = g0(xs) ∨ (¬f0(¬xs)∧¬f1(¬xs))  {- duality of g1 and f0∨f1 -}
                ⇔ f1(¬xs) = g0(xs) and f0(xs) = 1
                   {- f0(¬xs)=0 is impossible, because
                      it implies f1(¬xs)=g0(xs)∨¬f1(¬xs) and then
                      f1(¬xs)=g0(xs)=1 which contradicts condition (1.1) -}
              -}
             liftM (xs `IntSet.difference`) $ msum $ do
               is <- Set.toList f0
               let f' = Set.map (`IntSet.difference` is) f1
                   g' = Set.filter (is `disjoint`) g0
               return $ checkDualityB' (deleteRedundancy g') (deleteRedundancy f')
           ]
         else -- epsilon_v < min epsilon_x_f epsilon_x_g
           msum
           [ -- If x=0 then f(xs)=g(¬xs) ⇔ f1(xs) = g0(¬xs) ∨ g1(¬xs)
             checkDualityB' f1 (deleteRedundancy (g0 `Set.union` g1))
           , -- If x=1 then f(xs)=g(¬xs) ⇔ f0(xs) ∨ f1(xs) = g1(¬xs)
             liftM (IntSet.insert x) $ checkDualityB' (deleteRedundancy (f0 `Set.union` f1)) g1
           ]
  where
    size_f = Set.size f
    size_g = Set.size g
    v = size_f * size_g
    epsilon_v = 1 / xhi (fromIntegral v)
    xs = IntSet.unions $ Set.toList $ f `Set.union` g

-- $Redundancy
-- An implicant /I∈F/ of a DNF /F/ is redundant if /F/ contains proper subset of /I/.
-- A DNF /F/ is called redundant if it contains redundant implicants.
-- The main functions of this modules does not care about redundancy of DNFs.

test_condition_1_1_solve_L = xs `isCounterExampleOf` (f,g)
  where
    Just xs = condition_1_1_solve f g
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9], [4]]
    g = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9]]

test_condition_1_1_solve_R = xs `isCounterExampleOf` (f,g)
  where
    Just xs = condition_1_1_solve f g
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9]]
    g = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9], [4,7,8]]

test_condition_1_2_solve_L = xs `isCounterExampleOf` (f,g)
  where
    Just xs = condition_1_2_solve f g
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9,10]]
    g = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9]]

test_condition_1_2_solve_R = xs `isCounterExampleOf` (f,g)
  where
    Just xs = condition_1_2_solve f g
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9]]
    g = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9,10]]

test_condition_1_3_solve_L = xs `isCounterExampleOf` (f,g)
  where
    Just xs = condition_1_3_solve f g
    f = Set.fromList $ map IntSet.fromList [[2,4,7,10], [7,8], [9]]
    g = Set.fromList $ map IntSet.fromList [[7,9,10], [4,8,9], [2,8,9]]

test_condition_1_3_solve_R = xs `isCounterExampleOf` (f,g)
  where
    Just xs = condition_1_3_solve f g
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9,10]]
    g = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9,10]]

test_condition_2_1_solve_L = xs `isCounterExampleOf` (f,g)
  where
    Just xs = condition_2_1_solve f g
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [4,7,9], [7,8,9]]
    g = Set.fromList $ map IntSet.fromList [[2,4,7], [2,8,9], [4,8,9]]

test_condition_2_1_solve_R = xs `isCounterExampleOf` (f,g)
  where
    Just xs = condition_2_1_solve f g
    g = Set.fromList $ map IntSet.fromList [[2,4,7], [4,7,9], [7,8,9]]
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [2,8,9], [4,8,9]]

test_checkDualityA = checkDualityA f g == Nothing
  where
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9]]
    g = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9]]

test_checkDualityB = checkDualityA f g == Nothing
  where
    f = Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9]]
    g = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9]]
