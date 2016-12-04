{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Combinatorial.HittingSet.DAA
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- "Dualize and Advance" algorithm for enumerating maximal interesting sets
-- and minimal non-interesting sets.
--
-- * D. Gunopulos, H. Mannila, R. Khardon, and H. Toivonen, Data mining,
--   hypergraph transversals, and machine learning (extended abstract),
--   in Proceedings of the Sixteenth ACM SIGACT-SIGMOD-SIGART Symposium
--   on Principles of Database Systems, ser. PODS '97. 1997, pp. 209-216.
--   <http://almaden.ibm.com/cs/projects/iis/hdb/Publications/papers/pods97_trans.pdf>
-- 
-- * J. Bailey and P. Stuckey, Discovery of minimal unsatisfiable
--   subsets of constraints using hitting set dualization," in Practical
--   Aspects of Declarative Languages, pp. 174-186, 2005.
--   <http://ww2.cs.mu.oz.au/~pjs/papers/padl05.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.Combinatorial.HittingSet.DAA
  (
  -- * Problem definition
    IsProblem (..)
  , defaultGrow
  , defaultShrink
  , defaultMaximalInterestingSet
  , defaultMinimalUninterestingSet
  , SimpleProblem (..)

  -- * Main functionality
  , Options (..)
  , run

  -- * Applications
  , generateCNFAndDNF
  ) where

import Control.Monad
import Control.Monad.Identity
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

-- | Given a problem and an option, it computes maximal interesting sets and
-- minimal uninteresting sets.
run :: forall prob m. IsProblem prob m => prob -> Options m -> m (Set IntSet, Set IntSet)
run prob opt = loop (Set.map complement (optMaximalInterestingSets opt)) (optMinimalUninterestingSets opt)
  where
    univ :: IntSet
    univ = universe prob

    complement :: IntSet -> IntSet
    complement = (univ `IntSet.difference`)

    loop :: Set IntSet -> Set IntSet -> m (Set IntSet, Set IntSet)
    loop comp_pos neg = do
      xss <- liftM (`Set.difference` neg) $ optMinimalHittingSets opt comp_pos
      if Set.null xss then
        return (Set.map complement comp_pos, neg)
      else do
        (comp_pos',neg') <- loop2 comp_pos neg (Set.toList xss)
        loop comp_pos' neg'

    loop2 :: Set IntSet -> Set IntSet -> [IntSet] -> m (Set IntSet, Set IntSet)
    loop2 comp_pos neg [] = return (comp_pos, neg)
    loop2 comp_pos neg (xs : xss) = do
      ret <- maximalInterestingSet prob xs
      case ret of
        Nothing -> do          
          optOnMinimalUninterestingSetFound opt xs
          loop2 comp_pos (Set.insert xs neg) xss
        Just ys -> do
          optOnMaximalInterestingSetFound opt ys
          return (Set.insert (complement ys) comp_pos, neg)

-- | Compute the irredundant CNF representation and DNF representation.
--
-- Let /f/ be a monotone boolean function over set of variables /S/.
-- This function returns /C/ and /D/ where ∧_{I∈C} ∨_{i∈I} x_i and
-- ∨_{I∈D} ∧_{i∈I} x_i are the irredundant CNF representation /f/ and
-- DNF representation of /f/ respectively.
generateCNFAndDNF
  :: IntSet -- ^ Set of variables /V/
  -> (IntSet -> Bool) -- ^ A monotone boolean function /f/ from /{0,1}^|V| ≅ P(V)/ to @Bool@
  -> Set IntSet -- ^ Subset /C'/ of prime implicates /C/ of /f/
  -> Set IntSet -- ^ Subset /D'/ of prime implicants /D/ of /f/
  -> (Set IntSet, Set IntSet)
generateCNFAndDNF vs f cs ds = (Set.map (vs `IntSet.difference`) pos, neg)
  where
    prob = SimpleProblem vs (not . f)
    opt = def
      { optMaximalInterestingSets = Set.map (vs `IntSet.difference`) cs
      , optMinimalUninterestingSets = ds
      }
    (pos,neg) = runIdentity $ run prob opt
