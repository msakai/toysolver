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
  ( maximumMatching
  , minimumMatching
  , maximumPerfectMatching
  , minimumPerfectMatching
  ) where

import Control.Monad
import qualified Data.Foldable as F
import Data.Hashable
import Data.HashMap.Strict (HashMap, (!))
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import qualified ToySolver.Combinatorial.MaximumCardinalityBipartiteMatching as MaxCardMatching

-- | Maximum weight matching of bipartite graph
maximumMatching
  :: forall a b w. (Hashable a, Eq a, Hashable b, Eq b, Real w)
  => HashSet a -> HashSet b -> (a -> b -> w)
  -> (w, HashSet (a,b))
maximumMatching as bs w =
  case as_size `compare` bs_size of
    EQ ->
      case maximumPerfectMatching as bs w of
        (obj, sol, _) -> (obj, sol)
    GT ->
      let bs' = HashSet.map Right bs `HashSet.union` HashSet.fromList [Left i | i <- [1..(as_size-bs_size)]]
          w' _ (Left _)  = 0
          w' a (Right b) = w a b
      in case maximumPerfectMatching as bs' w' of
           (obj, sol, _) ->
             ( obj
             , HashSet.fromList [(a,b) | (a,Right b) <- HashSet.toList sol]
             )
    LT ->
      let as' = HashSet.map Right as `HashSet.union` HashSet.fromList [Left i | i <- [1..(bs_size-as_size)]]
          w' (Left _) _ = 0
          w' (Right a) b = w a b
      in case maximumPerfectMatching as' bs w' of
           (obj, sol, _) ->
             ( obj
             , HashSet.fromList [(a,b) | (Right a, b) <- HashSet.toList sol]
             )
  where
    as_size = HashSet.size as
    bs_size = HashSet.size bs

-- | Minimum weight matching of bipartite graph
minimumMatching
  :: forall a b w. (Hashable a, Eq a, Hashable b, Eq b, Real w)
  => HashSet a -> HashSet b -> (a -> b -> w)
  -> (w, HashSet (a,b))
minimumMatching as bs w =
  case maximumMatching as bs (\a b -> - w a b) of
    (obj, m) -> (- obj, m)

-- | Maximum weight perfect matching of complete bipartite graph.
--
-- The two sets must be same size.
maximumPerfectMatching
  :: forall a b w. (Hashable a, Eq a, Hashable b, Eq b, Real w)
  => HashSet a -> HashSet b -> (a -> b -> w)
  -> (w, HashSet (a,b), (HashMap a w, HashMap b w))
maximumPerfectMatching as bs w =
  case minimumPerfectMatching as bs (\a b -> - w a b) of
    (obj, m, (ysA,ysB)) -> (- obj, m, (HashMap.map negate ysA, HashMap.map negate ysB))

-- | Minimum weight perfect matching of complete bipartite graph.
--
-- The two sets must be same size.
minimumPerfectMatching
  :: forall a b w. (Hashable a, Eq a, Hashable b, Eq b, Real w)
  => HashSet a -> HashSet b -> (a -> b -> w)
  -> (w, HashSet (a,b), (HashMap a w, HashMap b w))
minimumPerfectMatching as bs _ | HashSet.size as /= HashSet.size bs = error "minimumPerfectMatching: two sets must be same size"
minimumPerfectMatching as bs w = loop m0 ys0
  where
    ys0 :: (HashMap a w, HashMap b w)
    ys0 = ( HashMap.fromList [(a, minimum [w a b | b <- HashSet.toList bs]) | a <- HashSet.toList as]
          , HashMap.fromList [(b, 0) | b <- HashSet.toList bs]
          )
    m0 = MaxCardMatching.solve as bs (equalityGraph ys0)

    loop
      :: HashSet (a,b) -> (HashMap a w, HashMap b w)
      -> (w, HashSet (a,b), (HashMap a w, HashMap b w))
    loop m ys@(ysA,ysB)
      | isPerfect m = (F.sum ysA + F.sum ysB, m, ys)
      | otherwise = loop m' ys'
      where
        b_exposed = bs `HashSet.difference` HashSet.map (\(_,b) -> b) m

        l :: HashSet (Either a b)
        l = go [Right b | b <- HashSet.toList b_exposed] HashSet.empty
          where
            g :: HashMap (Either a b) [Either a b]
            g = HashMap.fromListWith (++)
                [ if e `HashSet.member` m then (Left a, [Right b]) else (Right b, [Left a])
                | e@(a,b) <- HashSet.toList (equalityGraph ys)
                ]

            go :: [Either a b] -> HashSet (Either a b) -> HashSet (Either a b)
            go [] visited = visited
            go (v:vs) visited
              | v `HashSet.member` visited = go vs visited
              | otherwise = go (HashMap.lookupDefault [] v g ++ vs) (HashSet.insert v visited)

        -- augmenting dual solution
        ys' :: (HashMap a w, HashMap b w)
        ys' = (HashMap.mapWithKey f ysA, HashMap.mapWithKey g ysB)
          where
            f a val
              | not (Left a `HashSet.member` l) = val + slack
              | otherwise = val
            g b val
              | not (Right b `HashSet.member` l) = val - slack
              | otherwise = val
            slack = minimum
                    [ w u v - (ysA!u + ysB!v)
                    | u <- HashSet.toList as, not (Left u `HashSet.member` l)
                    , v <- HashSet.toList bs, Right v `HashSet.member` l
                    ]

        -- augmenting primal solution
        m' :: HashSet (a,b)
        m' = MaxCardMatching.solve' as bs (equalityGraph ys') m

    equalityGraph :: (HashMap a w, HashMap b w) -> HashSet (a,b)
    equalityGraph (ysA,ysB) = HashSet.fromList $ do
      a <- HashSet.toList as
      b <- HashSet.toList bs
      guard $ w a b == ysA!a + ysB!b
      return (a,b)

    isPerfect :: HashSet (a,b) -> Bool
    isPerfect m = F.all (`HashSet.member` as') as && F.all (`HashSet.member` bs') bs
      where
        as' = HashSet.map (\(a,_) -> a) m
        bs' = HashSet.map (\(_,b) -> b) m

test_minimumPerfectMatching = minimumPerfectMatching as bs (\a b -> w!(a,b))
  where
    as = HashSet.fromList [1,3]
    bs = HashSet.fromList [2,4]
    w :: HashMap (Int,Int) Int
    w = HashMap.fromList [((1,2),5),((1,4),2),((3,2),9),((3,4),3)]

test_minimumMatching = minimumMatching as bs (\a b -> w!(a,b))
  where
    as = HashSet.fromList [1,3,5]
    bs = HashSet.fromList [2,4]
    w :: HashMap (Int,Int) Int
    w = HashMap.fromList
        [ ((1,2),5), ((1,4),2)
        , ((3,2),9), ((3,4),3)
        , ((5,2),10), ((5,4),4)
        ]
