-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.MUS.Linear
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Minimal Unsatifiable Subset (MUS) Finder
--
-----------------------------------------------------------------------------
module ToySolver.SAT.MUS.Linear
  ( module ToySolver.SAT.MUS.Base
  , findMUSAssumptions
  ) where

import Control.Monad
import Data.Default.Class
import Data.List
import qualified Data.IntSet as IS
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
  log "computing a minimal unsatisfiable core by linear method"
  core <- liftM IS.fromList $ SAT.getFailedAssumptions solver
  log $ "initial core = " ++ showLits core
  update core
  if IS.null core then
    return core
  else
    loop core IS.empty

  where
    log :: String -> IO ()
    log = optLogger opt

    update :: US -> IO ()
    update = optUpdateBest opt

    showLit :: Lit -> String
    showLit = optShowLit opt

    showLits :: IS.IntSet -> String
    showLits ls = "{" ++ intercalate ", " (map showLit (IS.toList ls)) ++ "}"

    loop :: IS.IntSet -> IS.IntSet -> IO MUS
    loop ls1 fixed = do
      case IS.minView ls1 of
        Nothing -> do
          log $ "found a minimal unsatisfiable core"
          return fixed
        Just (l,ls) -> do
          log $ "trying to remove " ++ showLit l
          ret <- SAT.solveWith solver (IS.toList ls)
          if not ret then do
            ls2 <- liftM IS.fromList $ SAT.getFailedAssumptions solver
            let removed = ls1 `IS.difference` ls2
            log $ "successed to remove " ++ showLits removed
            log $ "new core = " ++ showLits (ls2 `IS.union` fixed)
            update ls2
            forM_ (IS.toList removed) $ \l ->
              SAT.addClause solver [-l]
            loop ls2 fixed
          else do
            log $ "failed to remove " ++ showLit l
            SAT.addClause solver [l]
            loop ls (IS.insert l fixed)
