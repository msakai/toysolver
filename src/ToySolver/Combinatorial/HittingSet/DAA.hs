{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
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
  -- * Main functionality
    IsProblem (..)
  , SimpleProblem (..)
  , Options (..)
  , run

  -- * Applications
  , generateCNFAndDNF
  ) where

import Control.Monad
import Control.Monad.Identity
import Data.Default.Class
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

  -- | If @xs@ is an interesting set @maximalInterestingSet prob xs@ returns @Just ys@
  -- such that ys is a maximall interesting superset of xs, otherwise it returns @Nothing@.
  maximalInterestingSet :: prob -> IntSet -> m (Maybe IntSet)
  maximalInterestingSet prob xs = do
   b <- isInteresting prob xs
   if not b then
     return Nothing
   else do
     let f ys z = do
           let ys' = IntSet.insert z ys
           b2 <- isInteresting prob ys'
           if b2 then return ys' else return ys
     liftM Just $ foldM f xs (IntSet.toList (universe prob `IntSet.difference` xs))

data SimpleProblem = SimpleProblem IntSet (IntSet -> Bool)

instance IsProblem SimpleProblem Identity where
  universe (SimpleProblem univ _) = univ
  isInteresting (SimpleProblem _ f) = return . f


data Options m
  = Options
  { optMinimalHittingSets :: Set IntSet -> m (Set IntSet)
  , optMaximalInterestingSets :: Set IntSet
  , optMinimalNoninterestingSets :: Set IntSet
  , optOnMaximalInterestingSetFound :: IntSet -> m ()
  , optOnMinimalNoninterestingSetFound :: IntSet -> m ()
  }

instance Monad m => Default (Options m) where
  def =
    Options
    { optMinimalHittingSets = return . HTC.minimalHittingSets
    , optMaximalInterestingSets = Set.empty
    , optMinimalNoninterestingSets = Set.empty
    , optOnMaximalInterestingSetFound = \_ -> return ()
    , optOnMinimalNoninterestingSetFound = \_ -> return ()
    }

-- | Given a problem and an option, it computes maximal interesting sets and
-- minimal non-interesting sets.
run :: forall prob m. IsProblem prob m => prob -> Options m -> m (Set IntSet, Set IntSet)
run prob opt = loop (Set.map complement (optMaximalInterestingSets opt)) (optMinimalNoninterestingSets opt)
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
          optOnMinimalNoninterestingSetFound opt xs
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
      , optMinimalNoninterestingSets = ds
      }
    (pos,neg) = runIdentity $ run prob opt
