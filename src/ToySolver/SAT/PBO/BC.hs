{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.PBO.BC
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
module ToySolver.SAT.PBO.BC
  ( solve
  ) where

import Control.Concurrent.STM
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.PBO.Context as C
import Text.Printf

solve :: C.Context cxt => cxt -> SAT.Solver -> IO ()
solve cxt solver = solveWBO (C.normalize cxt) solver

solveWBO :: C.Context cxt => cxt -> SAT.Solver -> IO ()
solveWBO cxt solver = do
  SAT.modifyConfig solver $ \config -> config{ SAT.configEnableBackwardSubsumptionRemoval = True }
  ub <- atomically $ C.getSearchUpperBound cxt
  loop (IntSet.fromList [lit | (lit,_) <- sels], IntSet.empty) (0, ub)

  where
    obj :: SAT.PBLinSum
    obj = C.getObjectiveFunction cxt

    sels :: [(SAT.Lit, Integer)]
    sels = [(-lit, w) | (w,lit) <- obj]

    weights :: SAT.LitMap Integer
    weights = IntMap.fromList sels

    loop :: (SAT.LitSet, SAT.LitSet) -> (Integer, Integer) -> IO ()
    loop (unrelaxed, relaxed) (lb, ub)
      | lb > ub = C.setFinished cxt
      | otherwise = do
          let mid = (lb + ub) `div` 2
          C.logMessage cxt $ printf "BC: %d <= obj <= %d; guessing obj <= %d" lb ub mid
          sel <- SAT.newVar solver
          SAT.addPBAtMostSoft solver sel [(weights IntMap.! lit, -lit) | lit <- IntSet.toList relaxed] mid
          ret <- SAT.solveWith solver (sel : IntSet.toList unrelaxed)
          if ret then do
            m <- SAT.getModel solver
            let val = C.evalObjectiveFunction cxt m
            let ub' = val - 1
            C.logMessage cxt $ printf "BC: updating upper bound: %d -> %d" ub ub'
            C.addSolution cxt m
            SAT.addClause solver [sel]
            SAT.addPBAtMost solver obj ub'
            loop (unrelaxed, relaxed) (lb, ub')
          else do
            core <- SAT.getFailedAssumptions solver
            SAT.addClause solver [-sel] -- delete temporary constraint
            let core2 = IntSet.fromList core `IntSet.intersection` unrelaxed
            if IntSet.null core2 then do
              C.logMessage cxt $ printf "BC: updating lower bound: %d -> %d" lb (mid+1)
              C.addLowerBound cxt (mid+1)
              loop (unrelaxed, relaxed) (mid+1, ub)
            else do
              let unrelaxed' = unrelaxed `IntSet.difference` core2
                  relaxed'   = relaxed `IntSet.union` core2
              C.logMessage cxt $ printf "BC: #unrelaxed=%d, #relaxed=%d" (IntSet.size unrelaxed') (IntSet.size relaxed')
              loop (unrelaxed', relaxed') (lb, ub)
