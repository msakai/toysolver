{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.PBO.BCD
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Reference:
--
-- * Federico Heras, Antonio Morgado, João Marques-Silva,
--   Core-Guided binary search algorithms for maximum satisfiability,
--   Twenty-Fifth AAAI Conference on Artificial Intelligence, 2011.
--   <http://www.aaai.org/ocs/index.php/AAAI/AAAI11/paper/view/3713>
--
-- * A. Morgado, F. Heras, and J. Marques-Silva,
--   Improvements to Core-Guided binary search for MaxSAT,
--   in Theory and Applications of Satisfiability Testing (SAT 2012),
--   pp. 284-297.
--   <https://doi.org/10.1007/978-3-642-31612-8_22>
--   <http://ulir.ul.ie/handle/10344/2771>
--
-----------------------------------------------------------------------------
module ToySolver.SAT.PBO.BCD
  ( solve
  ) where

import Control.Concurrent.STM
import Control.Monad
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import Data.List
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.PBO.Context as C
import Text.Printf

data CoreInfo
  = CoreInfo
  { coreLits :: SAT.LitSet
  , coreLB   :: !Integer
  , coreUB   :: !Integer
  }

coreMidValue :: CoreInfo -> Integer
coreMidValue c = (coreLB c + coreUB c) `div` 2

coreUnion :: CoreInfo -> CoreInfo -> CoreInfo
coreUnion c1 c2
  = CoreInfo
  { coreLits = IntSet.union (coreLits c1) (coreLits c2)
  , coreLB = coreLB c1 + coreLB c2
  , coreUB = coreUB c1 + coreUB c2
  }

solve :: C.Context cxt => cxt -> SAT.Solver -> IO ()
solve cxt solver = solveWBO (C.normalize cxt) solver

solveWBO :: C.Context cxt => cxt -> SAT.Solver -> IO ()
solveWBO cxt solver = do
  SAT.modifyConfig solver $ \config -> config{ SAT.configEnableBackwardSubsumptionRemoval = True }
  ub <- atomically $ C.getSearchUpperBound cxt
  loop (IntSet.fromList [lit | (lit,_) <- sels], IntSet.empty) [] ub

  where
    obj :: SAT.PBLinSum
    obj = C.getObjectiveFunction cxt

    sels :: [(SAT.Lit, Integer)]
    sels = [(-lit, w) | (w,lit) <- obj]

    weights :: SAT.LitMap Integer
    weights = IntMap.fromList sels

    coreNew :: SAT.LitSet -> CoreInfo
    coreNew cs = CoreInfo{ coreLits = cs, coreLB = 0, coreUB = sum [weights IntMap.! lit | lit <- IntSet.toList cs] }

    coreCostFun :: CoreInfo -> SAT.PBLinSum
    coreCostFun c = [(weights IntMap.! lit, -lit) | lit <- IntSet.toList (coreLits c)]

    loop :: (SAT.LitSet, SAT.LitSet) -> [CoreInfo] -> Integer -> IO ()
    loop (unrelaxed, relaxed) cores ub = do
      let lb = sum [coreLB info | info <- cores]
      C.logMessage cxt $ printf "BCD: %d <= obj <= %d" lb ub
      C.logMessage cxt $ printf "BCD: #cores=%d, #unrelaxed=%d, #relaxed=%d"
        (length cores) (IntSet.size unrelaxed) (IntSet.size relaxed)

      sels <- liftM IntMap.fromList $ forM cores $ \info -> do
        sel <- SAT.newVar solver
        SAT.addPBAtMostSoft solver sel (coreCostFun info) (coreMidValue info)
        return (sel, info)

      ret <- SAT.solveWith solver (IntMap.keys sels ++ IntSet.toList unrelaxed)

      if ret then do
        m <- SAT.getModel solver
        let val = C.evalObjectiveFunction cxt m
        let ub' = val - 1
        C.logMessage cxt $ printf "BCD: updating upper bound: %d -> %d" ub ub'
        C.addSolution cxt m
        SAT.addPBAtMost solver obj ub'
        let cores' = map (\info -> info{ coreUB = SAT.evalPBLinSum m (coreCostFun info) }) cores
        cont (unrelaxed, relaxed) cores' ub'
      else do
        core <- SAT.getFailedAssumptions solver
        case IntSet.toList core of
          [] -> return ()
          [sel] | Just info <- IntMap.lookup sel sels -> do
            let info'  = info{ coreLB = coreMidValue info + 1 }
                cores' = IntMap.elems $ IntMap.insert sel info' sels
            C.logMessage cxt $ printf "BCD: updating lower bound of a core"
            SAT.addPBAtLeast solver (coreCostFun info') (coreLB info') -- redundant, but useful for direct search
            cont (unrelaxed, relaxed) cores' ub
          _ -> do
            let torelax     = unrelaxed `IntSet.intersection` core
                intersected = [info | (sel,info) <- IntMap.toList sels, sel `IntSet.member` core]
                rest        = [info | (sel,info) <- IntMap.toList sels, sel `IntSet.notMember` core]
                mergedCore  = foldl' coreUnion (coreNew torelax) intersected
                unrelaxed'  = unrelaxed `IntSet.difference` torelax
                relaxed'    = relaxed `IntSet.union` torelax
                cores'      = mergedCore : rest
            if null intersected then do
              C.logMessage cxt $ printf "BCD: found a new core of size %d" (IntSet.size torelax)
            else do
              C.logMessage cxt $ printf "BCD: merging cores"
            SAT.addPBAtLeast solver (coreCostFun mergedCore) (coreLB mergedCore) -- redundant, but useful for direct search
            forM_ (IntMap.keys sels) $ \sel -> SAT.addClause solver [-sel] -- delete temporary constraints
            cont (unrelaxed', relaxed') cores' ub

    cont :: (SAT.LitSet, SAT.LitSet) -> [CoreInfo] -> Integer -> IO ()
    cont (unrelaxed, relaxed) cores ub
      | all (\info -> coreLB info > coreUB info) cores = C.setFinished cxt
      | otherwise = loop (unrelaxed, relaxed) cores ub
