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
-- This module provides functions for computing several kind of bipartite
-- matching. 
-- 
-- Reference:
--
-- * Friedrich Eisenbrand. “Linear and Discrete Optimization”.
--   <https://www.coursera.org/course/linearopt>
--
-----------------------------------------------------------------------------
module ToySolver.Combinatorial.BipartiteMatching
  ( 
  -- * Maximum cardinality bipartite matching
    maximumCardinalityMatching

  -- * Maximum weight bipartite matching
  , maximumWeightMatching
  , maximumWeightMatchingComplete

  -- * Maximum/Minimum weight bipartite perfect matching
  , maximumWeightPerfectMatching
  , minimumWeightPerfectMatching
  , maximumWeightPerfectMatchingComplete
  , minimumWeightPerfectMatchingComplete

  -- * Misc
  , minimumCardinalityEdgeCover
  , minimumWeightEdgeCover
  , minimumWeightEdgeCoverComplete
  ) where

import Control.Monad
import qualified Data.Foldable as F
import Data.IntMap.Strict (IntMap, (!))
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe

-- -----------------------------------------------------------------------------

-- | Maximum cardinality matching on a bipartite graph (A+B, E).
maximumCardinalityMatching
  :: IntSet      -- ^ vertex set A
  -> IntSet      -- ^ vertex set B
  -> [(Int,Int)] -- ^ set of edges E⊆A×B
  -> IntMap Int
maximumCardinalityMatching _as bs es = 
  case maximumCardinalityMatching' bs (\b -> IntMap.findWithDefault IntSet.empty b e_b2a) IntMap.empty of
    (m, _, _) -> m
  where
    e_b2a :: IntMap IntSet
    e_b2a = IntMap.fromListWith IntSet.union [(b, IntSet.singleton a) | (a,b) <- es]

-- | Alternating path b_0, a_0, …, b_{n-1}, a_{n-1}, b_n is represented as
-- (b_n, [(a_{n-1}, b_{n-1}) .. (a_0, b_0)], b_0).
type AlternatingPath = (Int, [(Int,Int)], Int)

-- | Augmenting path b_0, a_0, …, b_n, a_n is represented as
-- ([(a_n, b_n) .. (a_0, b_0)], b_0).
type AugmentingPath = ([(Int,Int)], Int)

-- | Internal low-level routine for maximum cardinality bipartite matching.
--
-- It returns a maximum cardinality matching M together with sets of
-- vertexes reachable from exposed B vertexes (b∈B such that ∀a∈A. (a,b)∉M)
-- on a directed graph (A+B, {a→b|(a,b)∈M}∪{b→a|(a,b)⊆E\\M}).
maximumCardinalityMatching'
  :: IntSet          -- ^ vertex set B
  -> (Int -> IntSet) -- ^ set of edges E⊆A×B represented as a mapping from B to 2^A.
  -> IntMap Int      -- ^ partial matching represented as an injective mapping from A to B
  -> (IntMap Int, IntSet, IntSet)
maximumCardinalityMatching' bs e_b2a m0 = loop m0 m0_b_exposed
  where
    m0_b_exposed = bs `IntSet.difference` IntSet.fromList (IntMap.elems m0)

    loop :: IntMap Int -> IntSet -> (IntMap Int, IntSet, IntSet)
    loop m m_b_exposed =
      case search m_b_exposed of
        (l_a, l_b, []) -> (m, l_a, l_b)
        (_, _, ds) ->
          let -- Note that IntMap.union is left-biased
              ds2 = [IntMap.fromList d2 | (d2,_) <- ds]
              m' = IntMap.unions ds2 `IntMap.union` m
              m_b_exposed' = m_b_exposed `IntSet.difference` IntSet.fromList [b0 | (_, b0) <- ds]
          in loop m' m_b_exposed'
      where
        search :: IntSet -> (IntSet, IntSet, [AugmentingPath])
        search b_exposed = loopB IntSet.empty b_exposed [(b, [], b) | b <- IntSet.toList b_exposed] [] []
          where
            loopB :: IntSet -> IntSet -> [AlternatingPath] -> [AlternatingPath] -> [AugmentingPath] -> (IntSet, IntSet, [AugmentingPath])
            loopB !visitedA !visitedB [] [] result = (visitedA, visitedB, result)
            loopB !visitedA !visitedB [] nextB result = loopB visitedA visitedB nextB [] result
            loopB !visitedA !visitedB ((b, d2, b0) : currB) nextB result = loopA visitedA visitedB (IntSet.toList (e_b2a b)) currB nextB result
              where
                loopA !visitedA !visitedB [] currB nextB result = loopB visitedA visitedB currB nextB result
                loopA !visitedA !visitedB (a:as) currB nextB result
                  | a `IntSet.member` visitedA = loopA visitedA visitedB as currB nextB result
                  | otherwise =
                      case IntMap.lookup a m of
                        Nothing ->
                          loopB (IntSet.insert a visitedA) visitedB (filter (\(_,_,b0') -> b0/=b0') currB) (filter (\(_,_,b0') -> b0/=b0') nextB) (((a,b) : d2, b0) : result)
                        Just b2
                          | b==b2 -> loopA visitedA visitedB as currB nextB result
                          | b2 `IntSet.member` visitedB -> loopA (IntSet.insert a visitedA) visitedB as currB nextB result
                          | otherwise -> loopA (IntSet.insert a visitedA) (IntSet.insert b2 visitedB) as currB ((b2, (a,b):d2, b0) : nextB) result

-- -----------------------------------------------------------------------------

-- | Maximum weight matching of a complete bipartite graph (A+B,A×B).
maximumWeightMatchingComplete
  :: forall w. (Real w)
  => IntSet            -- ^ vertex set A
  -> IntSet            -- ^ vertex set B
  -> (Int -> Int -> w) -- ^ weight of edges A×B
  -> (w, IntMap Int)
maximumWeightMatchingComplete as bs w =
  case maximumWeightMaximumMatchingComplete as bs (\a b -> max 0 (w a b)) of
    (_, m) ->
      let m' = IntMap.filterWithKey (\a b -> w a b > 0) m
      in (sum [w a b | (a,b) <- IntMap.toList m'], m')

-- | Maximum weight matching of a bipartite graph (A+B,E).
maximumWeightMatching
  :: forall w. (Real w)
  => IntSet          -- ^ vertex set A
  -> IntSet          -- ^ vertex set B
  -> [(Int, Int, w)] -- ^ edges E⊆A×B and their weights
  -> (w, IntMap Int)
maximumWeightMatching as bs w =
  case maximumWeightMaximumMatchingComplete as bs g of
    (_, m) ->
      let m' = IntMap.filterWithKey (\a b -> isJust (f a b)) m
      in (sum [g a b | (a,b) <- IntMap.toList m'], m')
  where
    tbl :: IntMap (IntMap w)
    tbl = IntMap.fromListWith IntMap.union [(a, (IntMap.singleton b v)) | (a,b,v) <- w]
    f a b = do
      t <- IntMap.lookup a tbl 
      v <- IntMap.lookup b t
      guard $ v >= 0
      return v
    g a b = fromMaybe 0 (f a b)

-- -----------------------------------------------------------------------------

-- | Maximum weight maximum matching of a complete bipartite graph (A+B,A×B).
maximumWeightMaximumMatchingComplete
  :: forall w. (Real w)
  => IntSet            -- ^ vertex set A
  -> IntSet            -- ^ vertex set B
  -> (Int -> Int -> w) -- ^ weight of edges A×B
  -> (w, IntMap Int)
maximumWeightMaximumMatchingComplete as bs w =
  case as_size `compare` bs_size of
    EQ ->
      case maximumWeightPerfectMatchingComplete as bs w of
        (obj, sol, _) -> (obj, sol)
    GT ->
      let bs' = bs `IntSet.union` IntSet.fromAscList (take (as_size-bs_size) $ filter (`IntSet.notMember` bs) [0..])
          w' a b
            | b `IntSet.member` bs = w a b
            | otherwise = 0
      in case maximumWeightPerfectMatchingComplete as bs' w' of
           (obj, sol, _) ->
             ( obj
             , IntMap.filterWithKey (\_ b -> b `IntSet.member` bs) sol
             )
    LT ->
      let as' = as `IntSet.union` IntSet.fromAscList (take (bs_size-as_size) $ filter (`IntSet.notMember` as) [0..])
          w' a b
            | a `IntSet.member` as = w a b
            | otherwise = 0
      in case maximumWeightPerfectMatchingComplete as' bs w' of
           (obj, sol, _) ->
             ( obj
             , IntMap.filterWithKey (\a _ -> a `IntSet.member` as) sol
             )
  where
    as_size = IntSet.size as
    bs_size = IntSet.size bs

-- -----------------------------------------------------------------------------

-- | Maximum weight perfect matching of a complete bipartite graph (A+B,A×B).
--
-- The two sets must be same size (\|A\| = \|B\|).
maximumWeightPerfectMatchingComplete
  :: forall w. (Real w)
  => IntSet            -- ^ vertex set A
  -> IntSet            -- ^ vertex set B
  -> (Int -> Int -> w) -- ^ weight of edges A×B
  -> (w, IntMap Int, (IntMap w, IntMap w))
maximumWeightPerfectMatchingComplete as bs w =
  case minimumWeightPerfectMatchingComplete as bs (\a b -> - w a b) of
    (obj, m, (ysA,ysB)) -> (- obj, m, (IntMap.map negate ysA, IntMap.map negate ysB))

-- | Minimum weight perfect matching of a complete bipartite graph (A+B,A×B).
--
-- The two sets must be same size (\|A\| = \|B\|).
minimumWeightPerfectMatchingComplete
  :: forall w. (Real w)
  => IntSet            -- ^ vertex set A
  -> IntSet            -- ^ vertex set B
  -> (Int -> Int -> w) -- ^ weight of edges A×B
  -> (w, IntMap Int, (IntMap w, IntMap w))
minimumWeightPerfectMatchingComplete as bs w
  | n /= IntSet.size bs = error "minimumWeightPerfectMatchingComplete: two sets must be same size"
  | otherwise = loop m0 ys0 (equalityGraph ys0)
  where
    n = IntSet.size as

    ys0 :: (IntMap w, IntMap w)
    ys0 = ( IntMap.fromSet (\a -> minimum [w a b | b <- IntSet.toList bs]) as
          , IntMap.fromSet (\_ -> 0) bs
          )
    m0 = IntMap.empty

    loop
      :: IntMap Int -> (IntMap w, IntMap w) -> IntMap IntSet
      -> (w, IntMap Int, (IntMap w, IntMap w))
    loop m_pre ys@(ysA,ysB) g_eq
      | IntMap.size m == n = (F.sum ysA + F.sum ysB, m, ys)
      | otherwise = loop m ys' g_eq'
      where
        (m, l_a, l_b) = maximumCardinalityMatching' bs (g_eq !) m_pre
        l_a' = as `IntSet.difference` l_a -- A \ L

        slack :: w
        slack = minimum
                [ w a b - (ysA!a + ysB!b)
                | a <- IntSet.toList l_a'
                , b <- IntSet.toList l_b
                ]

        -- augmenting dual solution
        ys' :: (IntMap w, IntMap w)
        ys' = (IntMap.mapWithKey f ysA, IntMap.mapWithKey g ysB)
          where
            f a val
              | a `IntSet.notMember` l_a = val + slack
              | otherwise = val
            g b val
              | b `IntSet.notMember` l_b = val - slack
              | otherwise = val

        g_eq' :: IntMap IntSet
        g_eq' = IntMap.mapWithKey f g_eq
          where
            f b as3
              | b `IntSet.member` l_b =
                  as3 `IntSet.union` IntSet.filter (\a -> w a b == (fst ys' ! a + snd ys' ! b)) l_a'
              | otherwise = as3 `IntSet.difference` l_a

    equalityGraph :: (IntMap w, IntMap w) -> IntMap IntSet
    equalityGraph (ysA,ysB) =
      IntMap.fromSet (\b -> IntSet.filter (\a -> w a b == ysA!a + ysB!b) as) bs

-- -----------------------------------------------------------------------------

-- | Maximum weight perfect matching of a complete bipartite graph (A+B,E).
--
-- If no such matching exist, it returns @Nothing@.
maximumWeightPerfectMatching
  :: forall w. (Real w)
  => IntSet        -- ^ vertex set A
  -> IntSet        -- ^ vertex set B
  -> [(Int,Int,w)] -- ^ edges E⊆A×B and their weights
  -> Maybe (w, IntMap Int, (IntMap w, IntMap w))
maximumWeightPerfectMatching as bs es = do
  (obj, m, (ysA,ysB)) <- minimumWeightPerfectMatching as bs [(a,b,-w) |(a,b,w) <- es]
  return (- obj, m, (IntMap.map negate ysA, IntMap.map negate ysB))

-- | Minimum weight perfect matching of a bipartite graph (A+B, E).
--
-- If no such matching exist, it returns @Nothing@.
minimumWeightPerfectMatching
  :: forall w. (Real w)
  => IntSet        -- ^ vertex set A
  -> IntSet        -- ^ vertex set B
  -> [(Int,Int,w)] -- ^ edges E⊆A×B and their weights
  -> Maybe (w, IntMap Int, (IntMap w, IntMap w))
minimumWeightPerfectMatching as bs es
  | n /= IntSet.size bs = Nothing
  | F.any IntMap.null e_b2a = Nothing
  | otherwise = loop m0 ys0 (equalityGraph ys0)
  where
    n = IntSet.size as

    -- Note that IntMap.union is left-biased.
    e_b2a :: IntMap (IntMap w)
    e_b2a = fmap IntMap.fromList $ IntMap.fromListWith (++) [(b,[(a,w)]) | (a,b,w) <- es]
              `IntMap.union` IntMap.fromSet (\_ -> []) bs
{-
    e_b2a = IntMap.fromListWith IntMap.union [(b, IntMap.singleton a w) | (a,b,w) <- es]
              `IntMap.union` IntMap.fromList [(b, IntMap.empty) | b <- IntSet.toList bs]
-}

    ys0 :: (IntMap w, IntMap w)
    ys0 = ( IntMap.fromSet (\_ -> 0) as
          , fmap F.minimum e_b2a
          )
    m0 = IntMap.empty

    loop
      :: IntMap Int -> (IntMap w, IntMap w) -> IntMap IntSet
      -> Maybe (w, IntMap Int, (IntMap w, IntMap w))
    loop m_pre ys@(ysA,ysB) g_eq
      | IntMap.size m == n = Just (F.sum ysA + F.sum ysB, m, ys)
      | null slacks = Nothing
      | otherwise = loop m ys' g_eq'
      where
        (m, l_a, l_b) = maximumCardinalityMatching' bs (g_eq !) m_pre

        slacks :: [w]
        slacks = [w - (ysA!a + ysB!b) | b <- IntSet.toList l_b, (a,w) <- IntMap.toList (e_b2a ! b), a `IntSet.notMember` l_a]

        slack :: w
        slack = minimum slacks

        -- augmenting dual solution
        ys' :: (IntMap w, IntMap w)
        ys' = (IntMap.mapWithKey f ysA, IntMap.mapWithKey g ysB)
          where
            f a val
              | a `IntSet.notMember` l_a = val + slack
              | otherwise = val
            g b val
              | b `IntSet.notMember` l_b = val - slack
              | otherwise = val

        g_eq' :: IntMap IntSet
        g_eq' = IntMap.mapWithKey f g_eq
          where
            f b as3
              | b `IntSet.member` l_b =
                  as3 `IntSet.union` IntSet.fromAscList [a | (a,w) <- IntMap.toAscList (e_b2a ! b), a `IntSet.notMember` l_a, w == fst ys' ! a + snd ys' ! b]
              | otherwise = as3 `IntSet.difference` l_a

    equalityGraph :: (IntMap w, IntMap w) -> IntMap IntSet
    equalityGraph (ysA,ysB) = IntMap.mapWithKey f e_b2a
      where
        f b xs = IntSet.fromAscList [a | (a,w) <- IntMap.toAscList xs, w == ysA!a + ysB!b]

-- -----------------------------------------------------------------------------

-- | Minimum cardinality edge cover of bipartite graph (A+B, E).
minimumCardinalityEdgeCover
  :: IntSet      -- ^ vertex set A
  -> IntSet      -- ^ vertex set B
  -> [(Int,Int)] -- ^ edges E⊆A×B
  -> Maybe (Set (Int,Int))
minimumCardinalityEdgeCover as bs es
  | IntMap.size ca /= IntSet.size as = Nothing
  | IntMap.size cb /= IntSet.size bs = Nothing
  | otherwise =
      case maximumCardinalityMatching as bs es of
        m -> 
          let ma = IntMap.keysSet m
              mb = IntSet.fromList $ IntMap.elems m
              m2 = Set.unions
                   [ Set.fromList (IntMap.toList m)
                   , Set.fromList [(a,b) | a <- IntSet.toList (as `IntSet.difference` ma), let b = ca IntMap.! a]
                   , Set.fromList [(a,b) | b <- IntSet.toList (bs `IntSet.difference` mb), let a = cb IntMap.! b]
                   ]
          in Just $ m2
  where
    ca = IntMap.fromList es
    cb = IntMap.fromList [(b,a) | (a,b) <- es]

-- | Minimum weight edge cover of bipartite graph (A+B, E).
minimumWeightEdgeCover
  :: forall w. (Real w)
  => IntSet        -- ^ vertex set A
  -> IntSet        -- ^ vertex set B
  -> [(Int,Int,w)] -- ^ edges E⊆A×B and their weights
  -> Maybe (Set (Int,Int))
minimumWeightEdgeCover as bs es
  | IntMap.size ca /= IntSet.size as = Nothing
  | IntMap.size cb /= IntSet.size bs = Nothing
  | otherwise =
      case maximumWeightMatching as' bs' es' of
        (_, m) ->
          let ma = IntMap.keysSet m
              mb = IntSet.fromList $ IntMap.elems m
              m2 = Set.unions
                   [ Set.fromList (IntMap.toList m)
                   , Set.fromList [(a,b) | a <- IntSet.toList (as `IntSet.difference` ma), let (b,_) = ca IntMap.! a]
                   , Set.fromList [(a,b) | b <- IntSet.toList (bs `IntSet.difference` mb), let (a,_) = cb IntMap.! b]
                   , Set.fromList [(a,b) | (a,b,w) <- es, w < 0]
                   ]
          in Just m2
  where
    minOnSnd xw1@(_,w1) xw2@(_,w2) = if w1 <= w2 then xw1 else xw2
    ca = IntMap.fromListWith minOnSnd [(a,(b,w)) | (a,b,w) <- es]
    cb = IntMap.fromListWith minOnSnd [(b,(a,w)) | (a,b,w) <- es]
    as' = IntSet.fromAscList [a | (a,(_,w)) <- IntMap.toAscList ca, w >= 0]
    bs' = IntSet.fromAscList [b | (b,(_,w)) <- IntMap.toAscList cb, w >= 0]
    es' = [(a, b, (snd (ca IntMap.! a) + snd (cb IntMap.! b)) - w) | (a,b,w) <- es, w >= 0]

-- | Minimum weight edge cover of complete bipartite graph (A+B, A×B).
minimumWeightEdgeCoverComplete
  :: forall w. (Real w)
  => IntSet            -- ^ vertex set A
  -> IntSet            -- ^ vertex set B
  -> (Int -> Int -> w) -- ^ weight of edges A×B
  -> Maybe (Set (Int,Int))
minimumWeightEdgeCoverComplete as bs w
  | IntMap.size ca /= IntSet.size as = Nothing
  | IntMap.size cb /= IntSet.size bs = Nothing
  | otherwise =
      case maximumWeightMatching as' bs' es' of
        (_, m) ->
          let ma = IntMap.keysSet m
              mb = IntSet.fromList $ IntMap.elems m
              m2 = Set.unions
                   [ Set.fromList (IntMap.toList m)
                   , Set.fromList [(a,b) | a <- IntSet.toList (as `IntSet.difference` ma), let (b,_) = ca IntMap.! a]
                   , Set.fromList [(a,b) | b <- IntSet.toList (bs `IntSet.difference` mb), let (a,_) = cb IntMap.! b]
                   , Set.fromList [(a,b) | a <- IntSet.toList as, b <- IntSet.toList bs, let w' = w a b, w' < 0]
                   ]
          in Just m2
  where
    minOnSnd xw1@(_,w1) xw2@(_,w2) = if w1 <= w2 then xw1 else xw2
    ca = IntMap.fromListWith minOnSnd [(a, (b, w a b)) | a <- IntSet.toList as, b <- IntSet.toList bs]
    cb = IntMap.fromListWith minOnSnd [(b, (a, w a b)) | a <- IntSet.toList as, b <- IntSet.toList bs]
    as' = IntSet.fromAscList [a | (a,(_,w)) <- IntMap.toAscList ca, w >= 0]
    bs' = IntSet.fromAscList [b | (b,(_,w)) <- IntMap.toAscList cb, w >= 0]
    es' = [ (a, b, (snd (ca IntMap.! a) + snd (cb IntMap.! b)) - w')
          | a <- IntSet.toList as, b <- IntSet.toList bs, let w' = w a b, w' >= 0 ]

-- -----------------------------------------------------------------------------
