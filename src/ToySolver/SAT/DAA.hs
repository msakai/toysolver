{-# OPTIONS_GHC -Wall #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.DAA
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- "Dualize and Advance" algorithm for finding minimal unsatisfiable sets.
--
-- * [DAA] J. Bailey and P. Stuckey, Discovery of minimal unsatisfiable
--   subsets of constraints using hitting set dualization," in Practical
--   Aspects of Declarative Languages, pp. 174-186, 2005.
--   <http://ww2.cs.mu.oz.au/~pjs/papers/padl05.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.SAT.DAA
  ( MUS
  , MCS
  , Options (..)
  , defaultOptions
  , allMCSAssumptions
  , allMUSAssumptions
  , daa
  ) where

import Control.Monad
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import qualified Data.Set as Set
import qualified ToySolver.HittingSet as HittingSet
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.Types
import ToySolver.SAT.CAMUS (Options (..), defaultOptions, MUS, MCS)

allMCSAssumptions :: SAT.Solver -> [Lit] -> Options -> IO [MCS]
allMCSAssumptions solver sels opt = do
  (_, mcses) <- daa solver sels opt
  return $ map IntSet.toList $ Set.toList mcses

allMUSAssumptions :: SAT.Solver -> [Lit] -> Options -> IO [MUS]
allMUSAssumptions solver sels opt = do
  (muses, _) <- daa solver sels opt
  return $ map IntSet.toList $ Set.toList muses

daa :: SAT.Solver -> [Lit] -> Options -> IO (Set LitSet, Set LitSet)
daa solver sels opt = loop Set.empty Set.empty
  where
    selsSet :: LitSet
    selsSet = IntSet.fromList sels

    loop :: Set LitSet -> Set LitSet -> IO (Set LitSet, Set LitSet)
    loop muses mcses = do
      let f muses [] = return (muses, mcses)
          f muses (xs:xss) = do
            ret <- findMSS xs
            case ret of
              Just mss -> do
                let mcs = selsSet `IntSet.difference` mss
                optOnMCSFound opt (IntSet.toList mcs)
                loop muses (Set.insert mcs mcses)
              Nothing -> do
                let mus = xs
                optOnMUSFound opt (IntSet.toList mus)
                SAT.addClause solver [-l | l <- IntSet.toList mus] -- lemma
                f (Set.insert mus muses) xss
      f muses (Set.toList (hst mcses `Set.difference` muses))

    hst :: Set LitSet -> Set LitSet
    hst = Set.fromList . map IntSet.fromList
        . HittingSet.minimalHittingSets
        . map IntSet.toList . Set.toList

    findMSS :: LitSet -> IO (Maybe LitSet)
    findMSS xs = do
      b <- SAT.solveWith solver (IntSet.toList xs)
      if b then do
        m <- SAT.model solver
        liftM Just $ grow $ IntSet.fromList [l | l <- sels, evalLit m l]
      else
        return Nothing

    grow :: LitSet -> IO LitSet
    grow xs = loop xs (selsSet `IntSet.difference` xs)
      where
        loop xs ys =
          case IntSet.minView ys of
            Nothing -> return xs
            Just (c, ys') -> do
              b <- SAT.solveWith solver (c : IntSet.toList xs)
              if b then do
                m <- SAT.model solver
                let cs = IntSet.fromList [l | l <- sels, evalLit m l]
                loop (xs `IntSet.union` cs) (ys' `IntSet.difference` cs)
              else
                loop xs ys'

{-
daa_min_unsat(U)
  bA := ∅
  bX := ∅
  X := ∅
  repeat
    M := grow(X,U);
    bX := bX ∪ {U - M}
    bN := HST (X)
    X := ∅
    for (S ∈ bN - bA)
      if (sat(S))
        X := S
        break
      else bA := bA ∪ {S}
    endfor
  until (X = ∅)
  return (bA)

grow(S,U)
  for (c ∈ U - S)
    if (sat(S ∪ {c})) S := S ∪ {c}
  endfor
  return(S)

Fig. 1. Dualize and advance algorithm for finding minimal unsatisfiable sets.
-}
