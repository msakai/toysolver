{-# LANGUAGE BangPatterns #-}
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
  ( findImplicateOrImplicant
  , minimalHittingSets
  , enumMinimalHittingSets
  ) where

import Control.Monad
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import qualified Data.Set as Set
import qualified ToySolver.Combinatorial.HittingSet.FredmanKhachiyan1996 as FredmanKhachiyan1996

-- | Find a new prime implicant or implicate.
--
-- Let /f/ be a monotone boolean function over set of variables /S/.
-- Let ∧_{I∈C} ∨_{i∈I} x_i and ∨_{I∈D} ∧_{i∈I} x_i be the irredundant
-- CNF representation /f/ and DNF representation of /f/ respectively.
--
-- Given a subset /C' ⊆ C/ and /D' ⊆ D/, @'findImplicateOrImplicant' S f C' D'@ returns
-- 
-- * @Just (Left I)@ where I ∈ C \\ C',
--
-- * @Just (Right I)@ where J ∈ D \\ D', or
--
-- * @Nothing@ if /C'=C/ and /D'=D/.
-- 
findImplicateOrImplicant
  :: IntSet -- ^ Set of variables /V/
  -> (IntSet -> Bool) -- ^ A monotone boolean function /f/ from /{0,1}^|V| ≅ P(V)/ to @Bool@
  -> Set IntSet -- ^ Subset /C'/ of prime implicates /C/ of /f/
  -> Set IntSet -- ^ Subset /D'/ of prime implicants /D/ of /f/
  -> Maybe (Either IntSet IntSet)
findImplicateOrImplicant vs f cs ds = do
  xs <- FredmanKhachiyan1996.checkDuality ds cs
  if f xs then do
    let loop :: [Int] -> IntSet -> IntSet
        loop [] !ret = ret
        loop (x:xs) !ret =
          if f (IntSet.delete x ret)
          then loop xs (IntSet.delete x ret)
          else loop xs ret
    return $ Right $ loop (IntSet.toList xs) xs
  else do
    let loop :: [Int] -> IntSet -> IntSet
        loop [] !ret = ret
        loop (x:xs) !ret =
          if f (IntSet.insert x ret)
          then loop xs ret
          else loop xs (IntSet.insert x ret)
    return $ Left $ (vs `IntSet.difference`) $ loop (IntSet.toList (vs `IntSet.difference` xs)) xs

minimalHittingSets :: Set IntSet -> Set IntSet
minimalHittingSets = Set.fromList . enumMinimalHittingSets

enumMinimalHittingSets :: Set IntSet -> [IntSet]
enumMinimalHittingSets dnf = loop Set.empty
  where
    vs = IntSet.unions $ Set.toList dnf
    f = evalDNF dnf

    loop :: Set IntSet -> [IntSet]
    loop cs =
      case findImplicateOrImplicant vs f cs dnf of
        Nothing -> []
        Just (Left c)  -> c : loop (Set.insert c cs)
        Just (Right d) -> error "GurvichKhachiyan1999.enumMinimalHittingSets: should not happen"

evalDNF :: Set IntSet -> IntSet -> Bool
evalDNF dnf xs = or [is `IntSet.isSubsetOf` xs | is <- Set.toList dnf]

evalCNF :: Set IntSet -> IntSet -> Bool
evalCNF cnf xs = and [not $ IntSet.null $ is `IntSet.intersection` xs | is <- Set.toList cnf]
 

f = Set.fromList $ map IntSet.fromList [[2,4,7], [7,8], [9]]
g = Set.fromList $ map IntSet.fromList [[7,9], [4,8,9], [2,8,9]]

testA1 = findImplicateOrImplicant (IntSet.fromList [2,4,7,8,9]) (evalDNF f) Set.empty f 
testA2 = findImplicateOrImplicant (IntSet.fromList [2,4,7,8,9]) (evalDNF f) (Set.singleton (IntSet.fromList [2,8,9])) f
testA3 = findImplicateOrImplicant (IntSet.fromList [2,4,7,8,9]) (evalDNF f) (Set.fromList [IntSet.fromList [2,8,9], IntSet.fromList [4,8,9]]) f
testA4 = findImplicateOrImplicant (IntSet.fromList [2,4,7,8,9]) (evalDNF f) (Set.fromList [IntSet.fromList [2,8,9], IntSet.fromList [4,8,9], IntSet.fromList [7,9]]) f

testB1 = findImplicateOrImplicant (IntSet.fromList [2,4,7,8,9]) (evalDNF f) g Set.empty
