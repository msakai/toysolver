-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.MUS.Insertion
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Minimal Unsatifiable Subset (MUS) Finder
--
-- References:
--
-- * <http://logos.ucd.ie/~jpms/talks/talksite/jpms-ismvl10.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.SAT.MUS.Insertion
  ( module ToySolver.SAT.MUS.Base
  , findMUSAssumptions
  ) where

import Control.Monad
import Data.Default.Class
import Data.List (intercalate)
import qualified Data.IntSet as IntSet
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.Types
import ToySolver.SAT.MUS.Base

-- | Find a minimal set of assumptions that causes a conflict.
-- Initial set of assumptions is taken from 'SAT.getFailedAssumptions'.
findMUSAssumptions
  :: SAT.Solver
  -> Options
  -> IO MUS
findMUSAssumptions solver opt = do
  log "computing a minimal unsatisfiable core by insertion method"
  core <- SAT.getFailedAssumptions solver
  log $ "initial core = " ++ showLits core
  update core
  if IntSet.null core then
    return core
  else do
    mus <- do
      b <- SAT.solve solver
      if b then
        loop IntSet.empty core
      else
        return IntSet.empty
    log $ "new core = " ++ showLits mus
    update mus
    return mus
  where
    log :: String -> IO ()
    log = optLogger opt

    update :: US -> IO ()
    update = optUpdateBest opt

    showLit :: Lit -> String
    showLit = optShowLit opt

    showLits :: IntSet.IntSet -> String
    showLits ls = "{" ++ intercalate ", " (map showLit (IntSet.toList ls)) ++ "}"

    loop :: IntSet.IntSet -> IntSet.IntSet -> IO MUS
    loop m f = do
      -- pre: (m∩f = ∅), (m⊎f is unsatisfiable), (f=∅ → m is unsatisfiable)
      case IntSet.minView f of
        Nothing -> return m
        Just (c, f') -> do
          -- m is satisfiable
          let loop2 s c = do
                -- pre: (m⊎s⊎{c} ⊆ f), (m⊎s is satisfiable)
                b <- SAT.solveWith solver (c : IntSet.toList (m `IntSet.union` s))
                if not b then do
                  -- c is a transition clause
                  log $ "found a transition constraint: " ++ showLit c
                  return (s,c)
                else do
                  model <- SAT.getModel solver
                  let s' = IntSet.filter (optEvalConstr opt model) f
                  case IntSet.minView (f `IntSet.difference` s') of
                    Nothing -> error "shuld not happen"
                    Just (c', _) -> loop2 s' c'
          (s,c') <- loop2 IntSet.empty c
          loop (IntSet.insert c' m) s
