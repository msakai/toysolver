{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Combinatorial.HittingSet.InterestingSets
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- * D. Gunopulos, H. Mannila, R. Khardon, and H. Toivonen, Data mining,
--   hypergraph transversals, and machine learning (extended abstract),
--   in Proceedings of the Sixteenth ACM SIGACT-SIGMOD-SIGART Symposium
--   on Principles of Database Systems, ser. PODS '97. 1997, pp. 209-216.
--   <http://almaden.ibm.com/cs/projects/iis/hdb/Publications/papers/pods97_trans.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.Combinatorial.HittingSet.InterestingSets
  (
  -- * Problem definition
    IsProblem (..)
  , defaultGrow
  , defaultShrink
  , defaultMaximalInterestingSet
  , defaultMinimalUninterestingSet
  , defaultMinimalUninterestingSetOrMaximalInterestingSet
  , SimpleProblem (..)

  -- * Options for maximal interesting sets enumeration
  , Options (..)
  ) where

import Control.Monad
import Data.Default.Class
import Data.Either
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import qualified Data.Set as Set
import qualified ToySolver.Combinatorial.HittingSet.Simple as HTC

-- | A problem is essentially a pair of an @IntSet@ (@universe@) and
-- a monotone pure function @IntSet -> Bool@ (@isInteresting@), but
-- we generalize a bit for potentialial optimization opportunity.
--
-- For simple cases you can just use 'SimpleProblem' instance.
class Monad m => IsProblem prob m | prob -> m where
  universe :: prob -> IntSet

  -- | Interesting sets are lower closed subsets of 'universe', i.e. if @xs@ is
  -- interesting then @ys@ ⊆ @xs@ is also interesting.
  isInteresting :: prob -> IntSet -> m Bool
  isInteresting prob xs = liftM isRight $ isInteresting' prob xs

  -- | If @xs@ is interesting it returns @Right ys@ where @ys@ is an interesting superset of @xs@.
  -- If @xs@ is uninteresting it returns @Left ys@ where @ys@ is an uninteresting subset of @xs@.
  isInteresting' :: prob -> IntSet -> m (Either IntSet IntSet)
  isInteresting' prob xs = do
    b <- isInteresting prob xs
    return $ if b then Right xs else Left xs

  -- | @grow xs@ computes maximal interesting set @ys@ that is a superset of @xs@.
  grow :: prob -> IntSet -> m IntSet
  grow = defaultGrow

  -- | @shrink xs@ computes minimal uninteresting set @ys@ that is a subset of @xs@.
  shrink :: prob -> IntSet -> m IntSet
  shrink = defaultShrink

  -- | If @xs@ is an interesting set @maximalInterestingSet prob xs@ returns @Just ys@
  -- such that @ys@ is a maximal interesting superset of @xs@, otherwise it returns @Nothing@.
  maximalInterestingSet :: prob -> IntSet -> m (Maybe IntSet)
  maximalInterestingSet = defaultMaximalInterestingSet

  -- | If @xs@ is an uninteresting set @minimalUninterestingSet prob xs@ returns @Just ys@
  -- such that @ys@ is a minimal uninteresting subset of @xs@, otherwise it returns @Nothing@.
  minimalUninterestingSet :: prob -> IntSet -> m (Maybe IntSet)
  minimalUninterestingSet = defaultMinimalUninterestingSet

  -- | If @xs@ is an uninteresting set @minimalUninterestingSetOrMaximalInterestingSet prob xs@ returns @Left ys@
  -- such that @ys@ is a minimal uninteresting subset of @xs@.
  -- If @xs@ is an interesting set @minimalUninterestingSetOrMaximalInterestingSet prob xs@ returns @Right ys@
  -- such that @ys@ is a maximal interesting superset of @xs@
  minimalUninterestingSetOrMaximalInterestingSet :: prob -> IntSet -> m (Either IntSet IntSet)
  minimalUninterestingSetOrMaximalInterestingSet = defaultMinimalUninterestingSetOrMaximalInterestingSet

  {-# MINIMAL universe, (isInteresting | isInteresting') #-}

-- | Default implementation of 'grow' using 'isInteresting''.
defaultGrow :: IsProblem prob m => prob -> IntSet -> m IntSet
defaultGrow prob xs = foldM f xs (IntSet.toList (universe prob `IntSet.difference` xs))
  where
    f xs' y = do
      ret <- isInteresting' prob (IntSet.insert y xs')
      case ret of
        Left _ -> return xs'
        Right xs'' -> return xs''

-- | Default implementation of 'shrink' using 'isInteresting''.
defaultShrink :: IsProblem prob m => prob -> IntSet -> m IntSet
defaultShrink prob xs = foldM f xs (IntSet.toList xs)
  where
    f xs' y = do
      ret <- isInteresting' prob (IntSet.delete y xs')
      case ret of
        Left xs'' -> return xs''
        Right _ -> return xs'

-- | Default implementation of 'maximalUninterestingSet' using 'isInteresting'' and 'grow'.
defaultMaximalInterestingSet :: IsProblem prob m => prob -> IntSet -> m (Maybe IntSet)
defaultMaximalInterestingSet prob xs = do
 ret <- isInteresting' prob xs
 case ret of
   Left _ -> return Nothing
   Right xs' -> liftM Just $ grow prob xs'

-- | Default implementation of 'minimalUninterestingSet' using 'isInteresting'' and 'shrink'.
defaultMinimalUninterestingSet :: IsProblem prob m => prob -> IntSet -> m (Maybe IntSet)
defaultMinimalUninterestingSet prob xs = do
 ret <- isInteresting' prob xs
 case ret of
   Left xs' -> liftM Just $ shrink prob xs'
   Right _ -> return Nothing

-- | Default implementation of 'minimalUninterestingSetOrMaximalInterestingSet' using 'isInteresting'', 'shrink' 'grow'.
defaultMinimalUninterestingSetOrMaximalInterestingSet
  :: IsProblem prob m => prob -> IntSet -> m (Either IntSet IntSet)
defaultMinimalUninterestingSetOrMaximalInterestingSet prob xs = do
 ret <- isInteresting' prob xs
 case ret of
   Left ys -> liftM Left $ shrink prob ys
   Right ys -> liftM Right $ grow prob ys

data SimpleProblem (m :: * -> *) = SimpleProblem IntSet (IntSet -> Bool)

instance Monad m => IsProblem (SimpleProblem m) m where
  universe (SimpleProblem univ _) = univ
  isInteresting (SimpleProblem _ f) = return . f

data Options m
  = Options
  { optMinimalHittingSets :: Set IntSet -> m (Set IntSet)
  , optMaximalInterestingSets :: Set IntSet
  , optMinimalUninterestingSets :: Set IntSet
  , optOnMaximalInterestingSetFound :: IntSet -> m ()
  , optOnMinimalUninterestingSetFound :: IntSet -> m ()
  }

instance Monad m => Default (Options m) where
  def =
    Options
    { optMinimalHittingSets = return . HTC.minimalHittingSets
    , optMaximalInterestingSets = Set.empty
    , optMinimalUninterestingSets = Set.empty
    , optOnMaximalInterestingSetFound = \_ -> return ()
    , optOnMinimalUninterestingSetFound = \_ -> return ()
    }
