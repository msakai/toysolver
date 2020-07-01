{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PB.Internal.Product
-- Copyright   :  (c) Masahiro Sakai 2018
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PB.Internal.Product
  ( decomposeToBinaryProducts
  ) where

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List hiding (insert)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Ord
import Data.Set (Set)
import qualified Data.Set as Set

import qualified ToySolver.Converter.PB.Internal.LargestIntersectionFinder as LargestIntersectionFinder

decomposeToBinaryProducts :: Set IntSet -> Map IntSet (IntSet,IntSet)
decomposeToBinaryProducts = decompose2 . decompose1

decompose1 :: Set IntSet -> Map IntSet (Maybe (IntSet,IntSet))
decompose1 ss = snd $ foldl' (flip f) (LargestIntersectionFinder.empty, Map.empty) ss'
  where
    ss' = map fst $ sortBy (comparing snd) [(s, IntSet.size s) | s <- Set.toList ss]

    f :: IntSet
      -> (LargestIntersectionFinder.Table, Map IntSet (Maybe (IntSet,IntSet)))
      -> (LargestIntersectionFinder.Table, Map IntSet (Maybe (IntSet,IntSet)))
    f s (t,r) | IntSet.size s < 2 || s `Map.member` r = (t,r)
    f s (t,r) =
      case LargestIntersectionFinder.findLargestIntersectionSet s t of
        Nothing ->
          ( LargestIntersectionFinder.insert s t
          , Map.insert s Nothing r
          )
        Just s0 ->
          let s1 = s `IntSet.intersection` s0
              s2 = s IntSet.\\ s1
           in if IntSet.size s1 < 2 && IntSet.size s2 < 2 then
                ( LargestIntersectionFinder.insert s t
                , Map.insert s Nothing r
                )
              else if IntSet.null s2 then -- i.e. s⊆s0
                case Map.lookup s0 r of
                  Nothing -> error "should not happen"
                  Just Nothing ->
                    let s3 = s0 IntSet.\\ s
                     in ( LargestIntersectionFinder.insert s3 $ LargestIntersectionFinder.insert s t
                        , -- union is left-biased
                          Map.insert s0 (Just (s, s3)) $
                            Map.union r (Map.fromList $ filter (\(s',_) -> IntSet.size s' >= 2) [(s, Nothing), (s3, Nothing)])
                        )
                  Just _ ->
                    ( LargestIntersectionFinder.insert s t
                    , Map.union r (Map.singleton s Nothing)
                    )
              else
                case f s2 (f s1 (t,r))  of
                   (t',r') ->
                     ( LargestIntersectionFinder.insert s t'
                     , Map.insert s (Just (s1,s2)) r'
                     )

decompose2 :: Map IntSet (Maybe (IntSet,IntSet)) -> Map IntSet (IntSet,IntSet)
decompose2 m = Map.fromList $ do
  (s,d) <- Map.toList m
  case d of
    Just (s1,s2) -> return (s, (s1,s2))
    Nothing -> f (IntSet.toList s) (IntSet.size s)
  where
    f s n
      | n < 2  = []
      | n == 2 = return (IntSet.fromList s, (IntSet.singleton (s !! 0), IntSet.singleton (s !! 1)))
      | otherwise =
          case splitAt (n `div` 2) s  of
            (s1, s2) -> (IntSet.fromList s, (IntSet.fromList s1, IntSet.fromList s2)) : f s1 (n `div` 2) ++ f s2 (n - (n `div` 2))
