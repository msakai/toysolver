{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PB.Internal.LargestIntersectionFinder
-- Copyright   :  (c) Masahiro Sakai 2018
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PB.Internal.LargestIntersectionFinder
  ( Table
  , empty
  , fromSet
  , fromList
  , toSet
  , toList
  , insert
  , findLargestIntersectionSet
  ) where

import Data.IntMap (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List hiding (insert)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Ord
import Data.Set (Set)
import qualified Data.Set as Set

data Table
  = Table
  { numSets   :: !Int
  , toSetId   :: Map IntSet SetId
  , fromSetId :: IntMap IntSet
  , invMember :: IntMap (IntMap Count) -- e ↦ {s ↦ 1 | e∈s}
  }
  deriving (Show)

type SetId = Int
type Count = Int

empty :: Table
empty =
  Table
  { numSets   = 0
  , toSetId   = Map.empty
  , fromSetId = IntMap.empty
  , invMember = IntMap.empty
  }

fromList :: [IntSet] -> Table
fromList = fromSet . Set.fromList

fromSet :: Set IntSet -> Table
fromSet ss =
  Table
  { numSets   = Set.size ss
  , toSetId   = Map.fromList [(s,i) | (i,s) <- l]
  , fromSetId = IntMap.fromList l
  , invMember =
      IntMap.unionsWith IntMap.union
        [ IntMap.fromAscList [(e, IntMap.singleton i 1) | e <- IntSet.toAscList s]
        | (i,s) <- l
        ]
  }
  where
    l = zip [0..] (Set.toList ss)

toSet :: Table -> Set IntSet
toSet = Map.keysSet . toSetId

toList :: Table -> [IntSet]
toList = Set.toList . toSet

insert :: IntSet -> Table -> Table
insert s t
  | s `Map.member` toSetId t = t
  | otherwise =
      t
      { numSets = n + 1
      , toSetId = Map.insert s n (toSetId t)
      , fromSetId = IntMap.insert n s (fromSetId t)
      , invMember =
          IntMap.unionWith IntMap.union
            (IntMap.fromAscList [(e, IntMap.singleton n 1) | e <- IntSet.toAscList s])
            (invMember t)
      }
  where
    n = numSets t

-- | Given a set S and a family of sets U, find a T∈S such that S∩T has maximum cardinality.
-- In case of tie, smaller T is preferred.
findLargestIntersectionSet :: IntSet -> Table -> Maybe IntSet
findLargestIntersectionSet s t
  | IntMap.null m =
      if IntSet.empty `Map.member` toSetId t
      then Just IntSet.empty
      else Nothing
  | otherwise = Just $! fromSetId t IntMap.! n
  where
    m :: IntMap Count
    m = IntMap.unionsWith (+) [IntMap.findWithDefault IntMap.empty e (invMember t) | e <- IntSet.toList s]
    (n,_,_) = maximumBy (comparing (\(_,c,_) -> c) <> flip (comparing (\(_,_,size) -> size))) $
                [(i, c, IntSet.size (fromSetId t IntMap.! i)) | (i,c) <- IntMap.toList m]
