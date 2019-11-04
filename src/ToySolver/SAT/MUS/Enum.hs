{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.MUS.Enum
-- Copyright   :  (c) Masahiro Sakai 2012-2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- In this module, we assume each soft constraint /C_i/ is represented as a literal.
-- If a constraint /C_i/ is not a literal, we can represent it as a fresh variable /v/
-- together with a hard constraint /v ⇒ C_i/.
--
-- References:
--
-- * [CAMUS] M. Liffiton and K. Sakallah, Algorithms for computing minimal
--   unsatisfiable subsets of constraints, Journal of Automated Reasoning,
--   vol. 40, no. 1, pp. 1-33, Jan. 2008. 
--   <http://sun.iwu.edu/~mliffito/publications/jar_liffiton_CAMUS.pdf>
--
-- * [HYCAM] A. Gregoire, B. Mazure, and C. Piette, Boosting a complete
--   technique to find MSS and MUS: thanks to a local search oracle, in
--   Proceedings of the 20th international joint conference on Artifical
--   intelligence, ser. IJCAI'07. San Francisco, CA, USA: Morgan Kaufmann
--   Publishers Inc., 2007, pp. 2300-2305.
--   <http://ijcai.org/papers07/Papers/IJCAI07-370.pdf>
--
-- * [DAA] J. Bailey and P. Stuckey, Discovery of minimal unsatisfiable
--   subsets of constraints using hitting set dualization," in Practical
--   Aspects of Declarative Languages, pp. 174-186, 2005.
--   <http://ww2.cs.mu.oz.au/~pjs/papers/padl05.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.SAT.MUS.Enum
  ( module ToySolver.SAT.MUS.Types
  , Method (..)
  , showMethod
  , parseMethod
  , Options (..)
  , allMUSAssumptions
  ) where

import Data.Char
import Data.Default.Class
import qualified Data.IntSet as IntSet
import Data.List (intercalate)
import qualified Data.Set as Set
import qualified ToySolver.Combinatorial.HittingSet.InterestingSets as I
import qualified ToySolver.Combinatorial.HittingSet.DAA as DAA
import qualified ToySolver.Combinatorial.HittingSet.MARCO as MARCO
import qualified ToySolver.Combinatorial.HittingSet.GurvichKhachiyan1999 as GurvichKhachiyan1999
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.Types
import ToySolver.SAT.MUS.Types
import ToySolver.SAT.MUS.Enum.Base
import qualified ToySolver.SAT.MUS.Enum.CAMUS as CAMUS

showMethod :: Method -> String
showMethod m = map toLower (show m)

parseMethod :: String -> Maybe Method
parseMethod s =
  case filter (/='-') $ map toLower s of
    "camus" -> Just CAMUS
    "daa" -> Just DAA
    "marco" -> Just MARCO
    "gurvichkhachiyan1999" -> Just GurvichKhachiyan1999
    _ -> Nothing

allMUSAssumptions :: SAT.Solver -> [Lit] -> Options -> IO ([MUS], [MCS])
allMUSAssumptions solver sels opt =
  case optMethod opt of
    CAMUS -> CAMUS.allMUSAssumptions solver sels opt
    DAA -> do
      (msses, muses) <- DAA.run prob opt2
      return (Set.toList muses, map mss2mcs (Set.toList msses))
    MARCO -> do
      (msses, muses) <- MARCO.run prob opt2
      return (Set.toList muses, map mss2mcs (Set.toList msses))
    GurvichKhachiyan1999 -> do
      (msses, muses) <- GurvichKhachiyan1999.run prob opt2
      return (Set.toList muses, map mss2mcs (Set.toList msses))
  where
    prob = Problem solver selsSet opt

    opt2 :: I.Options IO
    opt2 =
      (def :: I.Options IO)
      { I.optOnMaximalInterestingSetFound = \xs ->
          optOnMCSFound opt (mss2mcs xs)
      , I.optOnMinimalUninterestingSetFound = \xs ->
          optOnMUSFound opt xs
      }

    selsSet :: LitSet
    selsSet = IntSet.fromList sels

    mss2mcs :: LitSet -> LitSet
    mss2mcs = (selsSet `IntSet.difference`)

-- -----------------------------------------------------------------

data Problem = Problem SAT.Solver LitSet Options

instance I.IsProblem Problem IO where
  universe (Problem _ univ _) = univ

  isInteresting' (Problem solver univ opt) xs = do
    b <- SAT.solveWith solver (IntSet.toList xs)
    if b then do
      m <- SAT.getModel solver
      return $ I.InterestingSet $ IntSet.fromList [l | l <- IntSet.toList univ, optEvalConstr opt m l]
    else do
      zs <- SAT.getFailedAssumptions solver
      return $ I.UninterestingSet $ IntSet.fromList zs

  grow prob@(Problem _ _ opt) xs = do
    optLogger opt $ show (optMethod opt) ++ ": grow " ++ showLits prob xs
    ys <- I.defaultGrow prob xs
    optLogger opt $ show (optMethod opt) ++ ": grow added " ++ showLits prob (ys `IntSet.difference` xs)
    return ys

  shrink prob@(Problem _ _ opt) xs = do
    optLogger opt $ show (optMethod opt) ++ ": shrink " ++ showLits prob xs
    ys <- I.defaultShrink prob xs
    optLogger opt $ show (optMethod opt) ++ ": shrink deleted " ++ showLits prob (xs `IntSet.difference` ys)
    return ys

showLits :: Problem -> IntSet.IntSet -> String
showLits (Problem _ _ opt) ls =
  "{" ++ intercalate ", " (map (optShowLit opt) (IntSet.toList ls)) ++ "}"

-- -----------------------------------------------------------------
