{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.MUS.Enum.GurvichKhachiyan1999
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (MultiParamTypeClasses)
--
-----------------------------------------------------------------------------
module ToySolver.SAT.MUS.Enum.GurvichKhachiyan1999
  ( module ToySolver.SAT.MUS.Enum.Base
  , allMUSAssumptions
  ) where

import Data.Default.Class
import qualified Data.IntSet as IntSet
import Data.List (intercalate)
import qualified Data.Set as Set
import qualified ToySolver.Combinatorial.HittingSet.GurvichKhachiyan1999 as GurvichKhachiyan1999
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.Types
import ToySolver.SAT.MUS.Types
import ToySolver.SAT.MUS.Enum.Base

data Problem = Problem SAT.Solver LitSet Options

instance GurvichKhachiyan1999.IsProblem Problem IO where
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
    optLogger opt $ "GurvichKhachiyan1999: grow " ++ showLits prob xs
    ys <- GurvichKhachiyan1999.defaultGrow prob xs
    optLogger opt $ "GurvichKhachiyan1999: grow added " ++ showLits prob (ys `IntSet.difference` xs)
    return ys

  shrink prob@(Problem _ _ opt) xs = do
    optLogger opt $ "GurvichKhachiyan1999: shrink " ++ showLits prob xs
    ys <- GurvichKhachiyan1999.defaultShrink prob xs
    optLogger opt $ "GurvichKhachiyan1999: shrink deleted " ++ showLits prob (xs `IntSet.difference` ys)
    return ys

showLits :: Problem -> IntSet.IntSet -> String
showLits (Problem _ _ opt) ls =
  "{" ++ intercalate ", " (map (optShowLit opt) (IntSet.toList ls)) ++ "}"

allMUSAssumptions :: SAT.Solver -> [Lit] -> Options -> IO ([MUS], [MCS])
allMUSAssumptions solver sels opt = do
  (msses, muses) <- GurvichKhachiyan1999.run prob opt2
  return (Set.toList muses, map mss2mcs (Set.toList msses))
  where
    prob = Problem solver selsSet opt

    opt2 :: GurvichKhachiyan1999.Options IO
    opt2 =
      (def :: GurvichKhachiyan1999.Options IO)
      { GurvichKhachiyan1999.optOnMaximalInterestingSetFound = \xs ->
          optOnMCSFound opt (mss2mcs xs)
      , GurvichKhachiyan1999.optOnMinimalUninterestingSetFound = \xs ->
          optOnMUSFound opt xs
      }

    selsSet :: LitSet
    selsSet = IntSet.fromList sels

    mss2mcs :: LitSet -> LitSet
    mss2mcs = (selsSet `IntSet.difference`)
