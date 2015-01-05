{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.PBO.MSU4
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
module ToySolver.SAT.PBO.MSU4
  ( solve
  ) where

import Control.Concurrent.STM
import Control.Monad
import qualified Data.IntSet as IS
import qualified Data.IntMap as IM
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.PBO.Context as C
import Text.Printf

solve :: C.Context cxt => cxt -> SAT.Solver -> IO ()
solve cxt solver = solveWBO (C.normalize cxt) solver

solveWBO :: C.Context cxt => cxt -> SAT.Solver -> IO ()
solveWBO cxt solver = do
  SAT.setEnableBackwardSubsumptionRemoval solver True
  loop (IM.keysSet weights, IS.empty) 0

  where
    obj :: SAT.PBLinSum
    obj = C.getObjectiveFunction cxt

    sels :: [(SAT.Lit, Integer)]
    sels = [(-lit, w) | (w,lit) <- obj]

    weights :: SAT.LitMap Integer
    weights = IM.fromList sels
 
    loop :: (SAT.LitSet, SAT.LitSet) -> Integer -> IO ()
    loop (unrelaxed, relaxed) lb = do
      ret <- SAT.solveWith solver (IS.toList unrelaxed)
      if ret then do
        currModel <- SAT.getModel solver
        C.addSolution cxt currModel
        let violated = [weights IM.! l | l <- IS.toList relaxed, SAT.evalLit currModel l == False]
            currVal = sum violated
        SAT.addPBAtMost solver [(c,-l) | (l,c) <- sels] (currVal - 1)
        cont (unrelaxed, relaxed) lb
      else do
        core <- SAT.getFailedAssumptions solver
        let ls = IS.fromList core `IS.intersection` unrelaxed
        if IS.null ls then do
          C.setFinished cxt
        else do
          SAT.addClause solver [-l | l <- core] -- optional constraint but sometimes useful
          let min_weight = minimum [weights IM.! l | l <- IS.toList ls]
              lb' = lb + min_weight
          C.logMessage cxt $ printf "MSU4: found a core: size = %d, minimal weight = %d" (length core) min_weight 
          C.addLowerBound cxt lb'
          cont (unrelaxed `IS.difference` ls, relaxed `IS.union` ls) lb'

    cont :: (SAT.LitSet, SAT.LitSet) -> Integer -> IO ()
    cont (unrelaxed, relaxed) lb = do
      join $ atomically $ do
        b <- C.isFinished cxt
        return $ if b then return () else loop (unrelaxed, relaxed) lb
