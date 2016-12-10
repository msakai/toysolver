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
    module ToySolver.Combinatorial.HittingSet.InterestingSets

  -- * Main functionality
  , run

  -- * Applications: minimal hitting sets
  , generateCNFAndDNF
  ) where

import Control.Monad
import Control.Monad.Identity
import Data.Default.Class
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import qualified Data.Set as Set
import ToySolver.Combinatorial.HittingSet.InterestingSets

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
