{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  SAT.PBO.BC
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Core-Guided binary search algorithm.
--
-- Reference:
--
-- * Federico Heras, Antonio Morgado, João Marques-Silva,
--   Core-Guided binary search algorithms for maximum satisfiability,
--   Twenty-Fifth AAAI Conference on Artificial Intelligence, 2011.
--   <http://www.aaai.org/ocs/index.php/AAAI/AAAI11/paper/view/3713>
-- 
-----------------------------------------------------------------------------
module SAT.PBO.BC
  ( Options (..)
  , defaultOptions
  , solve
  ) where

import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import qualified SAT as SAT
import qualified SAT.Types as SAT
import Text.Printf

data Options
  = Options
  { optLogger      :: String -> IO ()
  , optUpdateBest  :: SAT.Model -> Integer -> IO ()
  , optUpdateLB    :: Integer -> IO ()
  , optInitialModel :: Maybe SAT.Model
  }

defaultOptions :: Options
defaultOptions
  = Options
  { optLogger     = \_ -> return ()
  , optUpdateBest = \_ _ -> return ()
  , optUpdateLB   = \_ -> return ()
  , optInitialModel = Nothing
  }

solve :: SAT.Solver -> SAT.PBLinSum -> Options -> IO (Maybe SAT.Model)
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
  case optInitialModel opt of
    Just m -> do
      loop (IntSet.fromList [lit | (lit,_) <- sels], IntSet.empty) (0, SAT.evalPBSum m obj - 1) (Just m)
    Nothing -> do
      loop (IntSet.fromList [lit | (lit,_) <- sels], IntSet.empty) (0, SAT.pbUpperBound obj) Nothing

  where
    weights :: SAT.LitMap Integer
    weights = IntMap.fromList sels

    obj :: SAT.PBLinSum
    obj = [(w, -lit) | (lit,w) <- sels]

    loop :: (SAT.LitSet, SAT.LitSet) -> (Integer, Integer) -> Maybe SAT.Model -> IO (Maybe SAT.Model)
    loop (unrelaxed, relaxed) (lb, ub) lastModel
      | lb > ub = return lastModel
      | otherwise = do
          let mid = (lb + ub) `div` 2
          logIO $ printf "BC: %d <= obj <= %d; guessing obj <= %d" lb ub mid
          sel <- SAT.newVar solver
          SAT.addPBAtMostSoft solver sel [(weights IntMap.! lit, -lit) | lit <- IntSet.toList relaxed] mid
          ret <- SAT.solveWith solver (sel : IntSet.toList unrelaxed)
          if ret then do
            m <- SAT.model solver
            let val = SAT.evalPBSum m obj
            optUpdateBest opt m val
            let ub' = val - 1
            logIO $ printf "BC: updating upper bound: %d -> %d" ub ub'
            SAT.addClause solver [sel]
            -- FIXME: improve backward subsumption removal to delete the old upper bound constraint of 
            SAT.addPBAtMost solver obj ub'
            loop (unrelaxed, relaxed) (lb, ub') (Just m)
          else do
            core <- SAT.failedAssumptions solver
            SAT.addClause solver [-sel] -- delete temporary constraint
            let core2 = IntSet.fromList core `IntSet.intersection` unrelaxed
            if IntSet.null core2 then do
              logIO $ printf "BC: updating lower bound: %d -> %d" lb (mid+1)
              optUpdateLB opt (mid+1)
              loop (unrelaxed, relaxed) (mid+1, ub) lastModel
            else do
              let unrelaxed' = unrelaxed `IntSet.difference` core2
                  relaxed'   = relaxed `IntSet.union` core2
              logIO $ printf "BC: #unrelaxed=%d, #relaxed=%d" (IntSet.size unrelaxed') (IntSet.size relaxed')
              loop (unrelaxed', relaxed') (lb, ub) lastModel

    logIO :: String -> IO ()
    logIO = optLogger opt
