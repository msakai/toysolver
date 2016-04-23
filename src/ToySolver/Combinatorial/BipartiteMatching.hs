{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Combinatorial.BipartiteMatching
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (ScopedTypeVariables, BangPatterns)
--
-- Reference:
--
-- * Friedrich Eisenbrand. “Linear and Discrete Optimization”.
--   <https://www.coursera.org/course/linearopt>
--
-----------------------------------------------------------------------------
module ToySolver.Combinatorial.BipartiteMatching
  ( maximumMatching
  , maximumMatching'
  , maximumWeightMaximumMatching
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

-- -----------------------------------------------------------------------------

maximumMatching
  :: forall a b. (Hashable a, Eq a, Hashable b, Eq b)
  => HashSet a -> HashSet b -> HashSet (a,b) -> HashSet (a,b)
maximumMatching as bs es = 
  case maximumMatching' as bs (\b -> HashMap.lookupDefault HashSet.empty b e_b2a) HashMap.empty of
    (m, _, _) -> HashSet.fromList $ HashMap.toList m
  where
    e_b2a :: HashMap b (HashSet a)
    e_b2a = HashMap.fromListWith HashSet.union [(b, HashSet.singleton a) | (a,b) <- HashSet.toList es]

-- | Internal low-level routine for maximum cardinality bipartite matching.
--
-- It returns a maximum cardinality matching M together with sets of
-- vertexes reachable from exposed B vertexes (b∈B such that ∀a∈A. (a,b)∉M)
-- on a directed graph of (A∪B, {a→b|(a,b)∈M}∪{b→a|(a,b)⊆E\\M}).
maximumMatching'
  :: forall a b. (Hashable a, Eq a, Hashable b, Eq b)
  => HashSet a        -- ^ vertex set A
  -> HashSet b        -- ^ vertex set B
  -> (b -> HashSet a) -- ^ set of edges E⊆A×B represented as a mapping from B to 2^A.
  -> HashMap a b      -- ^ partial matching represented as an injective mapping from A to B
  -> (HashMap a b, HashSet a, HashSet b)
maximumMatching' as bs e_b2a m0 = loop m0 m0_b_exposed
  where
    m0_b_exposed = bs `HashSet.difference` HashSet.fromList [b | (_,b) <- HashMap.toList m0]

    loop :: HashMap a b -> HashSet b -> (HashMap a b, HashSet a, HashSet b)
    loop m m_b_exposed =
      case search m_b_exposed of
        (l_a, l_b, []) -> (m, l_a, l_b)
        (_, _, ds) ->
          let -- Note that HashMap.union is left-biased
              ds2 = [HashMap.fromList d2 | (d2,_) <- ds]
              m' = HashMap.unions ds2 `HashMap.union` m
              m_b_exposed' = m_b_exposed `HashSet.difference` HashSet.fromList [b0 | (d2, b0) <- ds]
          in loop m' m_b_exposed'
      where
        search :: HashSet b -> (HashSet a, HashSet b, [([(a,b)], b)])
        search b_exposed = loopB HashSet.empty b_exposed [(b, [], b) | b <- HashSet.toList b_exposed] [] []
          where
            loopB :: HashSet a -> HashSet b -> [(b, [(a,b)], b)] -> [(b, [(a,b)], b)] -> [([(a,b)], b)] -> (HashSet a, HashSet b, [([(a,b)], b)])
            loopB !visitedA !visitedB [] [] result = (visitedA, visitedB, result)
            loopB !visitedA !visitedB [] nextB result = loopB visitedA visitedB nextB [] result
            loopB !visitedA !visitedB ((b, d2, b0) : currB) nextB result = loopA visitedA visitedB (HashSet.toList (e_b2a b)) currB nextB result
              where
                loopA !visitedA !visitedB [] currB nextB result = loopB visitedA visitedB currB nextB result
                loopA !visitedA !visitedB (a:as) currB nextB result
                  | a `HashSet.member` visitedA = loopA visitedA visitedB as currB nextB result
                  | otherwise =
                      case HashMap.lookup a m of
                        Nothing ->
                          loopB (HashSet.insert a visitedA) visitedB (filter (\(_,_,b0') -> b0/=b0') currB) (filter (\(_,_,b0') -> b0/=b0') nextB) (((a,b) : d2, b0) : result)
                        Just b2
                          | b==b2 -> loopA visitedA visitedB as currB nextB result
                          | b2 `HashSet.member` visitedB -> loopA (HashSet.insert a visitedA) visitedB as currB nextB result
                          | otherwise -> loopA (HashSet.insert a visitedA) (HashSet.insert b2 visitedB) as currB ((b2, (a,b):d2, b0) : nextB) result

test_maximumMatching = maximumMatching as bs es
  where
    as = HashSet.fromList ['a'..'e']
    bs :: HashSet Int
    bs = HashSet.fromList [1..5]
    es = HashSet.fromList [(a,b) | a <- HashSet.toList as, b <- HashSet.toList bs]

-- -----------------------------------------------------------------------------

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

-- -----------------------------------------------------------------------------

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
        (m, l_a, l_b) = maximumMatching' as bs (g_eq !) m_pre
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

-- -----------------------------------------------------------------------------

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
        (m, l_a, l_b) = maximumMatching' as bs (g_eq !) m_pre

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

-- -----------------------------------------------------------------------------

