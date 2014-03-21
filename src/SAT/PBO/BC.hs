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
  }

defaultOptions :: Options
defaultOptions
  = Options
  { optLogger     = \_ -> return ()
  , optUpdateBest = \_ _ -> return ()
  , optUpdateLB   = \_ -> return ()
  }

solve :: SAT.Solver -> SAT.PBLinSum -> Options -> IO (Maybe SAT.Model)
solve solver obj opt = solveWBO solver [(c,-lit) | (c,lit) <- obj] opt

solveWBO :: SAT.Solver -> [(Integer, SAT.Lit)] -> Options -> IO (Maybe SAT.Model)
solveWBO solver weights opt = do
  SAT.setEnableBackwardSubsumptionRemoval solver True
  loop (IntSet.fromList [lit | (_,lit) <- weights], IntSet.empty) (0, SAT.pbUpperBound obj) Nothing

  where
    weightsMap :: SAT.LitMap Integer
    weightsMap = IntMap.fromList [(lit,w) | (w,lit) <- weights]

    obj :: SAT.PBLinSum
    obj = [(w, -lit) | (w,lit) <- weights]

    loop :: (SAT.LitSet, SAT.LitSet) -> (Integer, Integer) -> Maybe SAT.Model -> IO (Maybe SAT.Model)
    loop (unrelaxed, relaxed) (lb, ub) lastModel
      | lb > ub = return lastModel
      | otherwise = do
          let mid = (lb + ub) `div` 2
          logIO $ printf "BC: %d <= obj <= %d; guessing obj <= %d" lb ub mid
          sel <- SAT.newVar solver
          SAT.addPBAtMostSoft solver sel [(weightsMap IntMap.! lit, -lit) | lit <- IntSet.toList relaxed] mid
          ret <- SAT.solveWith solver (sel : IntSet.toList unrelaxed)
          if ret then do
            m <- SAT.model solver
            let val = SAT.pbEval m obj
            optUpdateBest opt m val
            let ub' = val - 1
            logIO $ printf "BC: updating upper bound: %d -> %d" ub ub'
            -- Following constraints must be added in this order for backward subsumption removal.
            SAT.addClause solver [sel]
            SAT.addPBAtMost solver [(weightsMap IntMap.! lit, -lit) | lit <- IntSet.toList relaxed] ub'
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
