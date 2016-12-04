{-# OPTIONS_GHC -Wall #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.MUS.Enum.DAA
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
module ToySolver.SAT.MUS.Enum.DAA
  ( module ToySolver.SAT.MUS.Enum.Base
  , allMUSAssumptions
  ) where

import Control.Monad
import qualified Data.IntSet as IntSet
import Data.List (intercalate)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified ToySolver.Combinatorial.HittingSet.Simple as HittingSet
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.Types
import ToySolver.SAT.MUS.Types
import ToySolver.SAT.MUS.Enum.Base

allMUSAssumptions :: SAT.Solver -> [Lit] -> Options -> IO ([MUS], [MCS])
allMUSAssumptions solver sels opt =
  loop (Set.fromList (optKnownMUSes opt)) (Set.fromList (optKnownMCSes opt))
  where
    showLit :: Lit -> String
    showLit = optShowLit opt

    showLits :: IntSet.IntSet -> String
    showLits ls = "{" ++ intercalate ", " (map showLit (IntSet.toList ls)) ++ "}"

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

    checkSAT :: LitSet -> IO (Either LitSet LitSet)
    checkSAT xs = do
      b <- SAT.solveWith solver (IntSet.toList xs)
      if b then do
        m <- SAT.getModel solver
        return $ Right $ IntSet.fromList [l | l <- sels, optEvalConstr opt m l]
      else do
        zs <- SAT.getFailedAssumptions solver
        return $ Left $ IntSet.fromList zs

    findMSS :: LitSet -> IO (Maybe LitSet)
    findMSS xs = do
      forM_ sels $ \l -> do
        SAT.setVarPolarity solver (litVar l) (litPolarity l)
      optLogger opt $ "DAA: checking satisfiability of " ++ showLits xs
      ret <- checkSAT xs
      case ret of
        Right ys -> do
          optLogger opt $ "DAA: " ++ showLits xs ++ " is satisfiable"
          liftM Just $ grow ys
        Left _ -> do
          optLogger opt $ "DAA: " ++ showLits xs ++ " is unsatisfiable"
          SAT.addClause solver [-l | l <- IntSet.toList xs] -- lemma
          return Nothing

    grow :: LitSet -> IO LitSet
    grow xs = do
      ys <- loop xs (selsSet `IntSet.difference` xs)
      optLogger opt $ "DAA: grow " ++ showLits xs ++ " => " ++ showLits ys
      return ys
      where
        loop xs ys =
          case IntSet.minView ys of
            Nothing -> return xs
            Just (c, ys') -> do
              ret <- checkSAT (IntSet.insert c xs)
              case ret of
                Right cs -> loop (xs `IntSet.union` cs) (ys' `IntSet.difference` cs)
                Left zs -> do
                  SAT.addClause solver [-l | l <- IntSet.toList zs] -- lemma
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
