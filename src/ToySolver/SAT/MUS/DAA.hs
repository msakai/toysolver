{-# OPTIONS_GHC -Wall #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.MUS.DAA
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
module ToySolver.SAT.MUS.DAA
  ( module ToySolver.SAT.MUS.Types
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
import qualified ToySolver.Combinatorial.HittingSet.Simple as HittingSet
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.Types
import ToySolver.SAT.MUS.Types
import ToySolver.SAT.MUS.CAMUS (Options (..), defaultOptions)

allMCSAssumptions :: SAT.Solver -> [Lit] -> Options -> IO [MCS]
allMCSAssumptions solver sels opt = do
  (_, mcses) <- daa solver sels opt
  return mcses

allMUSAssumptions :: SAT.Solver -> [Lit] -> Options -> IO [MUS]
allMUSAssumptions solver sels opt = do
  (muses, _) <- daa solver sels opt
  return muses

daa :: SAT.Solver -> [Lit] -> Options -> IO ([MUS], [MCS])
daa solver sels opt =
  loop (Set.fromList (optKnownMUSes opt)) (Set.fromList (optKnownMCSes opt))
  where
    selsSet :: LitSet
    selsSet = IntSet.fromList sels

    loop :: Set LitSet -> Set LitSet -> IO ([MUS], [MCS])
    loop muses mcses = do
      let f muses [] = return (Set.toList muses, Set.toList mcses)
          f muses (xs:xss) = do
            ret <- findMSS xs
            case ret of
              Just mss -> do
                let mcs = selsSet `IntSet.difference` mss
                optOnMCSFound opt mcs
                loop muses (Set.insert mcs mcses)
              Nothing -> do
                let mus = xs
                optOnMUSFound opt mus
                f (Set.insert mus muses) xss
      f muses (Set.toList (HittingSet.minimalHittingSets mcses `Set.difference` muses))

    findMSS :: LitSet -> IO (Maybe LitSet)
    findMSS xs = do
      forM_ sels $ \l -> do
        SAT.setVarPolarity solver (litVar l) (litPolarity l)
      b <- SAT.solveWith solver (IntSet.toList xs)
      if b then do
        m <- SAT.getModel solver
        liftM Just $ grow $ IntSet.fromList [l | l <- sels, evalLit m l]
      else do
        SAT.addClause solver [-l | l <- IntSet.toList xs] -- lemma
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
                m <- SAT.getModel solver
                let cs = IntSet.fromList [l | l <- sels, evalLit m l]
                loop (xs `IntSet.union` cs) (ys' `IntSet.difference` cs)
              else do
                zs <- SAT.getFailedAssumptions solver
                SAT.addClause solver [-l | l <- zs] -- lemma
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
