{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Combinatorial.WeightedBipartiteMatching
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (ScopedTypeVariables)
--
-- Reference:
--
-- * Friedrich Eisenbrand. “Linear and Discrete Optimization”.
--   <https://www.coursera.org/course/linearopt>
--
-----------------------------------------------------------------------------
module ToySolver.Combinatorial.WeightedBipartiteMatching
  ( maximumWeightMaximumMatching
  , minimumWeightMaximumMatching
  , maximumWeightPerfectMatching
  , minimumWeightPerfectMatching
  , minimumWeightPerfectMatching'
  ) where

import Control.Monad
import qualified Data.Foldable as F
import Data.Hashable
import Data.HashMap.Strict (HashMap, (!))
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import qualified ToySolver.Combinatorial.MaximumCardinalityBipartiteMatching as MaxCardMatching

-- | Maximum weight maximum matching of a complete bipartite graph
maximumWeightMaximumMatching
  :: forall a b w. (Hashable a, Eq a, Hashable b, Eq b, Real w)
  => HashSet a -> HashSet b -> (a -> b -> w)
  -> (w, HashSet (a,b))
maximumWeightMaximumMatching as bs w =
  case as_size `compare` bs_size of
    EQ ->
      case maximumWeightPerfectMatching as bs w of
        (obj, sol, _) -> (obj, sol)
    GT ->
      let bs' = HashSet.map Right bs `HashSet.union` HashSet.fromList [Left i | i <- [1..(as_size-bs_size)]]
          w' _ (Left _)  = 0
          w' a (Right b) = w a b
      in case maximumWeightPerfectMatching as bs' w' of
           (obj, sol, _) ->
             ( obj
             , HashSet.fromList [(a,b) | (a,Right b) <- HashSet.toList sol]
             )
    LT ->
      let as' = HashSet.map Right as `HashSet.union` HashSet.fromList [Left i | i <- [1..(bs_size-as_size)]]
          w' (Left _) _ = 0
          w' (Right a) b = w a b
      in case maximumWeightPerfectMatching as' bs w' of
           (obj, sol, _) ->
             ( obj
             , HashSet.fromList [(a,b) | (Right a, b) <- HashSet.toList sol]
             )
  where
    as_size = HashSet.size as
    bs_size = HashSet.size bs

-- | Minimum weight maximum matching of a complete bipartite graph
minimumWeightMaximumMatching
  :: forall a b w. (Hashable a, Eq a, Hashable b, Eq b, Real w)
  => HashSet a -> HashSet b -> (a -> b -> w)
  -> (w, HashSet (a,b))
minimumWeightMaximumMatching as bs w =
  case maximumWeightMaximumMatching as bs (\a b -> - w a b) of
    (obj, m) -> (- obj, m)

-- | Maximum weight perfect matching of a complete bipartite graph.
--
-- The two sets must be same size.
maximumWeightPerfectMatching
  :: forall a b w. (Hashable a, Eq a, Hashable b, Eq b, Real w)
  => HashSet a -> HashSet b -> (a -> b -> w)
  -> (w, HashSet (a,b), (HashMap a w, HashMap b w))
maximumWeightPerfectMatching as bs w =
  case minimumWeightPerfectMatching as bs (\a b -> - w a b) of
    (obj, m, (ysA,ysB)) -> (- obj, m, (HashMap.map negate ysA, HashMap.map negate ysB))

-- | Minimum weight perfect matching of a complete bipartite graph.
--
-- The two sets must be same size.
minimumWeightPerfectMatching
  :: forall a b w. (Hashable a, Eq a, Hashable b, Eq b, Real w)
  => HashSet a -> HashSet b -> (a -> b -> w)
  -> (w, HashSet (a,b), (HashMap a w, HashMap b w))
minimumWeightPerfectMatching as bs w
  | n /= HashSet.size bs = error "minimumWeightPerfectMatching: two sets must be same size"
  | otherwise = loop m0 ys0 (equalityGraph ys0)
  where
    n = HashSet.size as

    ys0 :: (HashMap a w, HashMap b w)
    ys0 = ( HashMap.fromList [(a, minimum [w a b | b <- HashSet.toList bs]) | a <- HashSet.toList as]
          , HashMap.fromList [(b, 0) | b <- HashSet.toList bs]
          )
    m0 = HashMap.empty

    loop
      :: HashMap a b -> (HashMap a w, HashMap b w) -> HashMap b (HashSet a)
      -> (w, HashSet (a,b), (HashMap a w, HashMap b w))
    loop m_pre ys@(ysA,ysB) g_eq
      | HashMap.size m == n = (F.sum ysA + F.sum ysB, HashSet.fromList (HashMap.toList m), ys)
      | otherwise = loop m ys' g_eq'
      where
        (m, l_a, l_b) = MaxCardMatching.solve' as bs (g_eq !) m_pre
        l_a' = as `HashSet.difference` l_a -- A \ L

        slack :: w
        slack = minimum
                [ w u v - (ysA!u + ysB!v)
                | u <- HashSet.toList l_a'
                , v <- HashSet.toList l_b
                ]

        -- augmenting dual solution
        ys' :: (HashMap a w, HashMap b w)
        ys' = (HashMap.mapWithKey f ysA, HashMap.mapWithKey g ysB)
          where
            f a val
              | not (a `HashSet.member` l_a) = val + slack
              | otherwise = val
            g b val
              | not (b `HashSet.member` l_b) = val - slack
              | otherwise = val

        g_eq' :: HashMap b (HashSet a)
        g_eq' = HashMap.mapWithKey f g_eq
          where
            f b as3
              | b `HashSet.member` l_b =
                  as3 `HashSet.union` HashSet.filter (\a -> w a b == (fst ys' ! a + snd ys' ! b)) l_a'
              | otherwise = as3 `HashSet.difference` l_a

    equalityGraph :: (HashMap a w, HashMap b w) -> HashMap b (HashSet a)
    equalityGraph (ysA,ysB) =
      HashMap.fromList
      [ (b, HashSet.fromList [a | a <- HashSet.toList as, w a b == ysA!a + ysB!b])
      | b <- HashSet.toList bs
      ]

-- | Minimum weight perfect matching of a bipartite graph.
--
-- The two sets must be same size.
minimumWeightPerfectMatching'
  :: forall a b w. (Hashable a, Eq a, Hashable b, Eq b, Real w)
  => HashSet a -> HashSet b -> [(a,b,w)]
  -> Maybe (w, HashSet (a,b), (HashMap a w, HashMap b w))
minimumWeightPerfectMatching' as bs es
  | n /= HashSet.size bs = error "minimumWeightPerfectMatching: two sets must be same size"
  | F.any HashMap.null e_b2a = Nothing
  | otherwise = loop m0 ys0 (equalityGraph ys0)
  where
    n = HashSet.size as

    -- Note that HashMap.union is left-biased.
    e_b2a :: HashMap b (HashMap a w)
    e_b2a = fmap HashMap.fromList $ HashMap.fromListWith (++) [(b,[(a,w)]) | (a,b,w) <- es]
              `HashMap.union` HashMap.fromList [(b,[]) | b <- HashSet.toList bs]
{-
    e_b2a = HashMap.fromListWith HashMap.union [(b, HashMap.singleton a w) | (a,b,w) <- es]
              `HashMap.union` HashMap.fromList [(b, HashMap.empty) | b <- HashSet.toList bs]
-}

    ys0 :: (HashMap a w, HashMap b w)
    ys0 = ( HashMap.fromList [(a, 0) | a <- HashSet.toList as]
          , HashMap.fromList [(b, minimum (HashMap.elems xs)) | (b,xs) <- HashMap.toList e_b2a]
          )
    m0 = HashMap.empty

    loop
      :: HashMap a b -> (HashMap a w, HashMap b w) -> HashMap b (HashSet a)
      -> Maybe (w, HashSet (a,b), (HashMap a w, HashMap b w))
    loop m_pre ys@(ysA,ysB) g_eq
      | HashMap.size m == n = Just (F.sum ysA + F.sum ysB, HashSet.fromList (HashMap.toList m), ys)
      | null slacks = Nothing
      | otherwise = loop m ys' g_eq'
      where
        (m, l_a, l_b) = MaxCardMatching.solve' as bs (g_eq !) m_pre

        slacks :: [w]
        slacks = [w - (ysA!a + ysB!b) | b <- HashSet.toList l_b, (a,w) <- HashMap.toList (e_b2a ! b), not (a `HashSet.member` l_a)]

        slack :: w
        slack = minimum slacks

        -- augmenting dual solution
        ys' :: (HashMap a w, HashMap b w)
        ys' = (HashMap.mapWithKey f ysA, HashMap.mapWithKey g ysB)
          where
            f a val
              | not (a `HashSet.member` l_a) = val + slack
              | otherwise = val
            g b val
              | not (b `HashSet.member` l_b) = val - slack
              | otherwise = val

        g_eq' :: HashMap b (HashSet a)
        g_eq' = HashMap.mapWithKey f g_eq
          where
            f b as3
              | b `HashSet.member` l_b =
                  as3 `HashSet.union` HashSet.fromList [a | (a,w) <- HashMap.toList (e_b2a ! b), not (a `HashSet.member` l_a), w == fst ys' ! a + snd ys' ! b]
              | otherwise = as3 `HashSet.difference` l_a

    equalityGraph :: (HashMap a w, HashMap b w) -> HashMap b (HashSet a)
    equalityGraph (ysA,ysB) = HashMap.mapWithKey f e_b2a
      where
        f b xs = HashSet.fromList [a | (a,w) <- HashMap.toList xs, w == ysA!a + ysB!b]


test_minimumWeightPerfectMatching = minimumWeightPerfectMatching as bs (\a b -> w!(a,b))
  where
    as = HashSet.fromList [1,3]
    bs = HashSet.fromList [2,4]
    w :: HashMap (Int,Int) Int
    w = HashMap.fromList [((1,2),5),((1,4),2),((3,2),9),((3,4),3)]

test_minimumWeightMaximumMatching = minimumWeightMaximumMatching as bs (\a b -> w!(a,b))
  where
    as = HashSet.fromList [1,3,5]
    bs = HashSet.fromList [2,4]
    w :: HashMap (Int,Int) Int
    w = HashMap.fromList
        [ ((1,2),5), ((1,4),2)
        , ((3,2),9), ((3,4),3)
        , ((5,2),10), ((5,4),4)
        ]
