{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.MUS.Enum.DAA
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (MultiParamTypeClasses)
--
-- "Dualize and Advance" algorithm for finding minimal unsatisfiable sets.
--
-- * [DAA] J. Bailey and P. Stuckey, Discovery of minimal unsatisfiable
--   subsets of constraints using hitting set dualization," in Practical
--   Aspects of Declarative Languages, pp. 174-186, 2005.
--   <http://ww2.cs.mu.oz.au/~pjs/papers/padl05.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.SAT.MUS.Enum.DAA
  ( module ToySolver.SAT.MUS.Enum.Base
  , allMUSAssumptions
  ) where

import Data.Default.Class
import qualified Data.IntSet as IntSet
import Data.List (intercalate)
import qualified Data.Set as Set
import qualified ToySolver.Combinatorial.HittingSet.Simple as HittingSet
import qualified ToySolver.Combinatorial.HittingSet.DAA as DAA
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.Types
import ToySolver.SAT.MUS.Types
import ToySolver.SAT.MUS.Enum.Base

data Problem = Problem SAT.Solver LitSet Options

instance DAA.IsProblem Problem IO where
  universe (Problem _ univ _) = univ

  isInteresting' (Problem solver univ opt) xs = do
    b <- SAT.solveWith solver (IntSet.toList xs)
    if b then do
      m <- SAT.getModel solver
      return $ Right $ IntSet.fromList [l | l <- IntSet.toList univ, optEvalConstr opt m l]
    else do
      zs <- SAT.getFailedAssumptions solver
      return $ Left $ IntSet.fromList zs

  grow prob@(Problem _ _ opt) xs = do
    optLogger opt $ "DAA: grow " ++ showLits prob xs
    ys <- DAA.defaultGrow prob xs
    optLogger opt $ "DAA: grow added " ++ showLits prob (ys `IntSet.difference` xs)
    return ys

showLits :: Problem -> IntSet.IntSet -> String
showLits (Problem _ _ opt) ls =
  "{" ++ intercalate ", " (map (optShowLit opt) (IntSet.toList ls)) ++ "}"

allMUSAssumptions :: SAT.Solver -> [Lit] -> Options -> IO ([MUS], [MCS])
allMUSAssumptions solver sels opt = do
  (msses, muses) <- DAA.run prob opt2
  return (Set.toList muses, map mss2mcs (Set.toList msses))
  where
    prob = Problem solver selsSet opt

    opt2 :: DAA.Options IO
    opt2 =
      (def :: DAA.Options IO)
      { DAA.optMinimalHittingSets = return . HittingSet.minimalHittingSets
      , DAA.optOnMaximalInterestingSetFound = \xs ->
          optOnMCSFound opt (mss2mcs xs)
      , DAA.optOnMinimalUninterestingSetFound = \xs ->
          optOnMUSFound opt xs
      }

    selsSet :: LitSet
    selsSet = IntSet.fromList sels

    mss2mcs :: LitSet -> LitSet
    mss2mcs = (selsSet `IntSet.difference`)

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
