{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  SAT.PBO.MSU4
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
-- 
-- Reference:
--
-- * João P. Marques-Silva and Jordi Planes.
--   Algorithms for Maximum Satisfiability using Unsatisfiable Cores.
--   In Design, Automation and Test in Europe, 2008 (DATE '08). March 2008.
--   pp. 408-413, doi:10.1109/date.2008.4484715.
--   <http://dx.doi.org/10.1109/date.2008.4484715>
--   <http://eprints.soton.ac.uk/265000/1/jpms-date08.pdf>
--   <http://www.csi.ucd.ie/staff/jpms/talks/talksite/jpms-date08.pdf>
--
-----------------------------------------------------------------------------
module SAT.PBO.MSU4
  ( Options (..)
  , defaultOptions
  , solve
  ) where

import qualified Data.IntSet as IS
import qualified Data.IntMap as IM
import qualified SAT as SAT
import qualified SAT.Types as SAT

import Text.Printf

data Options
  = Options
  { optLogger      :: String -> IO ()
  , optUpdateBest  :: SAT.Model -> Integer -> IO ()
  , optUpdateLB    :: Integer -> IO ()
  }

defaultOptions :: Options
defaultOptions
  = Options
  { optLogger     = \_ -> return ()
  , optUpdateBest = \_ _ -> return ()
  , optUpdateLB   = \_ -> return ()
  }

solve :: SAT.Solver -> [(Integer, SAT.Lit)] -> Options -> IO (Maybe SAT.Model)
solve solver obj opt = solveWBO solver [(-v, c) | (c,v) <- obj'] opt'
  where
    (obj',offset) = SAT.normalizePBSum (obj,0)
    opt' =
      opt
      { optUpdateBest = \m val -> optUpdateBest opt m (offset + val)
      , optUpdateLB   = \val -> optUpdateLB opt (offset + val)
      }

solveWBO :: SAT.Solver -> [(SAT.Lit, Integer)] -> Options -> IO (Maybe SAT.Model)
solveWBO solver sels opt = do
  SAT.setEnableBackwardSubsumptionRemoval solver True
  optUpdateLB opt 0
  loop (IM.keysSet weights, IS.empty) 0 Nothing

  where
    weights = IM.fromList sels
    
    loop :: (SAT.LitSet, SAT.LitSet) -> Integer -> Maybe (SAT.Model, Integer) -> IO (Maybe SAT.Model)
    loop (unrelaxed, relaxed) lb best = do
      ret <- SAT.solveWith solver (IS.toList unrelaxed)
      if ret then do
        currModel <- SAT.model solver
        let violated = [weights IM.! l | l <- IS.toList relaxed, SAT.evalLit currModel l == False]
            currVal = sum violated
        best' <-
          case best of
            Just (_, bestVal)
              | currVal < bestVal -> do
                  optUpdateBest opt currModel currVal
                  return $ Just (currModel, currVal)
              | otherwise -> do
                  return best
            Nothing -> do
              optUpdateBest opt currModel currVal
              return $ Just (currModel, currVal)
        SAT.addPBAtMost solver [(c,-l) | (l,c) <- sels] (currVal - 1)
        cont (unrelaxed, relaxed) lb best'
      else do
        core <- SAT.failedAssumptions solver
        let ls = IS.fromList core `IS.intersection` unrelaxed
        if IS.null ls then do
          return (fmap fst best)
        else do
          SAT.addClause solver [-l | l <- core] -- optional constraint but sometimes useful
          let min_weight = minimum [weights IM.! l | l <- IS.toList ls]
              lb' = lb + min_weight
          optLogger opt $ printf "MSU4: found a core: size = %d, minimal weight = %d" (length core) min_weight 
          optUpdateLB opt lb'
          cont (unrelaxed `IS.difference` ls, relaxed `IS.union` ls) lb' best

    cont :: (SAT.LitSet, SAT.LitSet) -> Integer -> Maybe (SAT.Model, Integer) -> IO (Maybe SAT.Model)
    cont _ lb (Just (bestModel, bestVal)) | lb == bestVal  = return (Just bestModel)
    cont (unrelaxed, relaxed) lb best = loop (unrelaxed, relaxed) lb best
