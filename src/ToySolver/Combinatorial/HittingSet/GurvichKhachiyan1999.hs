{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Combinatorial.HittingSet.GurvichKhachiyan1999
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- References:
--
-- * [GurvichKhachiyan1999] Vladimir Gurvich and Leonid Khachiyan,
--   On generating the irredundant conjunctive and disjunctive normal forms of monotone Boolean functions,
--   Discrete Applied Mathematics, vol. 96-97, pp. 363-373, 1999.
--   <http://www.sciencedirect.com/science/article/pii/S0166218X99000992>
--
-----------------------------------------------------------------------------
module ToySolver.Combinatorial.HittingSet.GurvichKhachiyan1999
  (
  -- * Problem definition
    module ToySolver.Combinatorial.HittingSet.InterestingSets

  -- * Main functionality
  , run

  -- * Applications: monotone boolean functions
  , findPrimeImplicateOrPrimeImplicant
  , generateCNFAndDNF

  -- * Applicaitons: minimal hitting sets
  , minimalHittingSets
  , enumMinimalHittingSets
  ) where

import Control.Monad.Identity
import Data.Default.Class
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import qualified Data.Set as Set
import qualified ToySolver.Combinatorial.HittingSet.FredmanKhachiyan1996 as FredmanKhachiyan1996
import ToySolver.Combinatorial.HittingSet.InterestingSets

-- -----------------------------------------------------------------

-- | Given a problem and an option, it computes maximal interesting sets and
-- minimal uninteresting sets.
run :: forall m prob. IsProblem prob m => prob -> Options m -> m (Set IntSet, Set IntSet)
run prob opt = loop (Set.map complement (optMaximalInterestingSets opt)) (optMinimalUninterestingSets opt)
  where
    univ :: IntSet
    univ = universe prob

    complement :: IntSet -> IntSet
    complement = (univ `IntSet.difference`)

    loop :: Set IntSet -> Set IntSet -> m (Set IntSet, Set IntSet)
    loop comp_pos neg = do
      case FredmanKhachiyan1996.checkDuality neg comp_pos of
        Nothing -> return (Set.map complement comp_pos, neg)
        Just xs -> do
          ret <- minimalUninterestingSetOrMaximalInterestingSet prob xs
          case ret of
            UninterestingSet ys -> do
              optOnMinimalUninterestingSetFound opt ys
              loop comp_pos (Set.insert ys neg)
            InterestingSet ys -> do
              optOnMaximalInterestingSetFound opt ys
              loop (Set.insert (complement ys) comp_pos) neg

-- -----------------------------------------------------------------

-- | Find a new prime implicant or implicate.
--
-- Let /f/ be a monotone boolean function over set of variables /S/.
-- Let ∧_{I∈C} ∨_{i∈I} x_i and ∨_{I∈D} ∧_{i∈I} x_i be the irredundant
-- CNF representation /f/ and DNF representation of /f/ respectively.
--
-- Given a subset /C' ⊆ C/ and /D' ⊆ D/, @'findPrimeImplicateOrPrimeImplicant' S f C' D'@ returns
-- 
-- * @Just (Left I)@ where I ∈ C \\ C',
--
-- * @Just (Right I)@ where J ∈ D \\ D', or
--
-- * @Nothing@ if /C'=C/ and /D'=D/.
-- 
findPrimeImplicateOrPrimeImplicant
  :: IntSet -- ^ Set of variables /V/
  -> (IntSet -> Bool) -- ^ A monotone boolean function /f/ from /{0,1}^|V| ≅ P(V)/ to @Bool@
  -> Set IntSet -- ^ Subset /C'/ of prime implicates /C/ of /f/
  -> Set IntSet -- ^ Subset /D'/ of prime implicants /D/ of /f/
  -> Maybe ImplicateOrImplicant
findPrimeImplicateOrPrimeImplicant vs f cs ds = do
  xs <- FredmanKhachiyan1996.checkDuality ds cs
  let prob = SimpleProblem vs (not . f)
  case runIdentity (minimalUninterestingSetOrMaximalInterestingSet prob xs) of
    UninterestingSet ys -> return (Implicant ys)
    InterestingSet ys -> return (Implicate (vs `IntSet.difference` ys))

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

minimalHittingSets :: Set IntSet -> Set IntSet
minimalHittingSets = Set.fromList . enumMinimalHittingSets

enumMinimalHittingSets :: Set IntSet -> [IntSet]
enumMinimalHittingSets dnf = loop Set.empty
  where
    vs = IntSet.unions $ Set.toList dnf
    f = evalDNF dnf

    loop :: Set IntSet -> [IntSet]
    loop cs =
      case findPrimeImplicateOrPrimeImplicant vs f cs dnf of
        Nothing -> []
        Just (Implicate c)  -> c : loop (Set.insert c cs)
        Just (Implicant _) -> error "GurvichKhachiyan1999.enumMinimalHittingSets: should not happen"

evalDNF :: Set IntSet -> IntSet -> Bool
evalDNF dnf xs = or [is `IntSet.isSubsetOf` xs | is <- Set.toList dnf]

_evalCNF :: Set IntSet -> IntSet -> Bool
_evalCNF cnf xs = and [not $ IntSet.null $ is `IntSet.intersection` xs | is <- Set.toList cnf]


_f, _g :: Set IntSet
_f = Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9]]
_g = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9]]

_testA1, _testA2, _testA3, _testA4 :: Maybe ImplicateOrImplicant
_testA1 = findPrimeImplicateOrPrimeImplicant (IntSet.fromList [2,4,7,8,9]) (evalDNF _f) Set.empty _f
_testA2 = findPrimeImplicateOrPrimeImplicant (IntSet.fromList [2,4,7,8,9]) (evalDNF _f) (Set.singleton (IntSet.fromList [2,8,9])) _f
_testA3 = findPrimeImplicateOrPrimeImplicant (IntSet.fromList [2,4,7,8,9]) (evalDNF _f) (Set.fromList [IntSet.fromList [2,8,9], IntSet.fromList [4,8,9]]) _f
_testA4 = findPrimeImplicateOrPrimeImplicant (IntSet.fromList [2,4,7,8,9]) (evalDNF _f) (Set.fromList [IntSet.fromList [2,8,9], IntSet.fromList [4,8,9], IntSet.fromList [7,9]]) _f

_testB1 :: Maybe ImplicateOrImplicant
_testB1 = findPrimeImplicateOrPrimeImplicant (IntSet.fromList [2,4,7,8,9]) (evalDNF _f) _g Set.empty
