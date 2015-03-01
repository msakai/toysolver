-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.MUS.QuickXplain
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Minimal Unsatifiable Subset (MUS) Finder based on QuickXplain algorithm.
--
-- References:
--
-- * Ulrich Junker. QuickXplain: Preferred explanations and relaxations for
--   over-constrained problems. In Proc. of AAAI’04, pages 167-172, 2004.
--   <http://www.aaai.org/Papers/AAAI/2004/AAAI04-027.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.SAT.MUS.QuickXplain
  ( module ToySolver.SAT.MUS.Types
  , Options (..)
  , defaultOptions
  , findMUSAssumptions
  ) where

import Control.Monad
import Data.Default.Class
import Data.List
import qualified Data.IntSet as IS
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.Types
import ToySolver.SAT.MUS.Types
import ToySolver.SAT.MUS hiding (findMUSAssumptions)

-- | Find a minimal set of assumptions that causes a conflict.
-- Initial set of assumptions is taken from 'SAT.getFailedAssumptions'.
findMUSAssumptions
  :: SAT.Solver
  -> Options
  -> IO MUS
findMUSAssumptions solver opt = do
  log "computing a minimal unsatisfiable core"
  core <- liftM IS.fromList $ SAT.getFailedAssumptions solver
  update $ IS.toList core
  log $ "core = " ++ showLits core
  if IS.null core then
    return core
  else
    f IS.empty False core

  where
    log :: String -> IO ()
    log = optLogger opt

    update :: [Lit] -> IO ()
    update = optUpdateBest opt

    showLit :: Lit -> String
    showLit = optLitPrinter opt

    showLits :: IS.IntSet -> String
    showLits ls = "{" ++ intercalate ", " (map showLit (IS.toList ls)) ++ "}"

    -- Precondition:
    -- * bs∪cs is unsatisfiable
    -- * ¬hasDelta ⇒ bs is satisfiable
    --
    -- Returns:
    -- * minimal subset S⊆cs such that bs∪S is unsatisfiable
    -- 
    f :: IS.IntSet -> Bool -> IS.IntSet -> IO IS.IntSet
    f bs hasDelta cs = do
      log $ "checking satisfiability of " ++ showLits bs
      ret <- if not hasDelta then do
               return True
             else
               SAT.solveWith solver (IS.toList bs)
      if not ret then do
        log $ showLits bs ++ " is unsatisfiable"
        log $ "new core = " ++ showLits bs
        update $ IS.toList bs
        return IS.empty
      else do
        log $ showLits bs ++ " is satisfiable"
        let s = IS.size cs
        if s == 1 then do
          return cs
        else do
          let cs' = IS.toAscList cs
              cs1 = IS.fromAscList $ take (s `div` 2) cs'
              cs2 = IS.fromAscList $ drop (s `div` 2) cs'
          log $ "splitting " ++ showLits cs ++ " into " ++ showLits cs1 ++ " and " ++ showLits cs2
          ds2 <- f (bs `IS.union` cs1) (not (IS.null cs1)) cs2
          ds1 <- f (bs `IS.union` ds2) (not (IS.null ds2)) cs1
          return (ds1 `IS.union` ds2)

{-
Algorithm QUICKXPLAIN(B, C, ≺)
 1. if isConsistent(B ∪ C) return 'no conflict';
 2. else if C = ∅ then return ∅;
 3. else return QUICKXPLAIN'(B, B, C, ≺);

Algorithm QUICKXPLAIN'(B, ∆, C, ≺)
 4. if ∆ ≠ ∅ and not isConsistent(B) then return ∅;
 5. if C = {α} then return {α};
 6. let α_1, …, α_n be an enumeration of C that respects ≺;
 7. let k be split(n) where 1 ≤ k < n;
 8. C1 := {α_1, …, α_k} and C2 := {α_{k+1}, …, α_n};
 9. ∆2 := QUICKXPLAIN'(B ∪ C1, C1, C2, ≺);
10. ∆1 := QUICKXPLAIN'(B ∪ ∆2, ∆2, C1, ≺);
11. return ∆1 ∪ ∆2;
-}