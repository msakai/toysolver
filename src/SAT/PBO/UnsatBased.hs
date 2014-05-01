{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  SAT.PBO.UnsatBased
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (BangPatterns)
-- 
-- Reference:
--
-- * Vasco Manquinho Ruben Martins Inês Lynce
--   Improving Unsatisfiability-based Algorithms for Boolean Optimization.
--   Theory and Applications of Satisfiability Testing – SAT 2010, pp 181-193.
--   <http://dx.doi.org/10.1007/978-3-642-14186-7_16>
--   <http://sat.inesc-id.pt/~ruben/papers/manquinho-sat10.pdf>
--   <http://sat.inesc-id.pt/~ruben/talks/sat10-talk.pdf>
--
-----------------------------------------------------------------------------
module SAT.PBO.UnsatBased
  ( solve
  ) where

import Control.Monad
import qualified Data.IntMap as IntMap
import qualified SAT as SAT
import qualified SAT.Types as SAT
import qualified SAT.PBO.Context as C

solve :: C.Context cxt => cxt -> SAT.Solver -> IO ()
solve cxt solver = solveWBO (C.normalize cxt) solver

solveWBO :: C.Context cxt => cxt -> SAT.Solver -> IO ()
solveWBO cxt solver = do
  SAT.setEnableBackwardSubsumptionRemoval solver True
  let sels0 = [(-v, c) | (c,v) <- C.getObjectiveFunction cxt]
  loop 0 (IntMap.fromList sels0)
  where
    loop :: Integer -> SAT.LitMap Integer -> IO ()
    loop !lb sels = do
      C.addLowerBound cxt lb

      ret <- SAT.solveWith solver (IntMap.keys sels)
      if ret then do
        m <- SAT.model solver
        -- モデルから余計な変数を除去する?
        C.addSolution cxt m
        return ()
      else do
        core <- SAT.failedAssumptions solver
        case core of
          [] -> C.setFinished cxt
          _  -> do
            let !min_c = minimum [sels IntMap.! sel | sel <- core]
                !lb' = lb + min_c

            xs <- forM core $ \sel -> do
              r <- SAT.newVar solver
              return (sel, r)
            SAT.addExactly solver (map snd xs) 1
            SAT.addClause solver [-l | l <- core] -- optional constraint but sometimes useful

            ys <- liftM IntMap.unions $ forM xs $ \(sel, r) -> do
              sel' <- SAT.newVar solver
              SAT.addClause solver [-sel', r, sel]
              let c = sels IntMap.! sel
              if c > min_c
                then return $ IntMap.fromList [(sel', min_c), (sel, c - min_c)]
                else return $ IntMap.singleton sel' min_c
            let sels' = IntMap.union ys (IntMap.difference sels (IntMap.fromList [(sel, ()) | sel <- core]))

            loop lb' sels'
