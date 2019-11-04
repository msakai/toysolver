{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.PBO.BCD2
-- Copyright   :  (c) Masahiro Sakai 2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
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
module ToySolver.SAT.PBO.BCD2
  ( Options (..)
  , solve
  ) where

import Control.Concurrent.STM
import Control.Monad
import Data.IORef
import Data.Default.Class
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.PBO.Context as C
import qualified ToySolver.Combinatorial.SubsetSum as SubsetSum
import Text.Printf

-- | Options for BCD2 algorithm.
--
-- The default value can be obtained by 'def'.
data Options
  = Options
  { optEnableHardening :: Bool
  , optEnableBiasedSearch :: Bool
  , optSolvingNormalFirst :: Bool
  }

instance Default Options where
  def =
    Options
    { optEnableHardening = True
    , optEnableBiasedSearch = True
    , optSolvingNormalFirst = True
    }

data CoreInfo
  = CoreInfo
  { coreLits :: SAT.LitSet
  , coreLBRef :: !(IORef Integer)
  , coreUBSelectors :: !(IORef (Map Integer SAT.Lit))
  }

newCoreInfo :: SAT.LitSet -> Integer -> IO CoreInfo
newCoreInfo lits lb = do
  lbRef <- newIORef lb
  selsRef <- newIORef Map.empty
  return
    CoreInfo
    { coreLits = lits
    , coreLBRef = lbRef
    , coreUBSelectors = selsRef
    }

deleteCoreInfo :: SAT.Solver -> CoreInfo -> IO ()
deleteCoreInfo solver core = do
  m <- readIORef (coreUBSelectors core)
  -- Delete soft upperbound constraints by fixing selector variables
  forM_ (Map.elems m) $ \sel ->
    SAT.addClause solver [-sel]

getCoreLB :: CoreInfo -> IO Integer
getCoreLB = readIORef . coreLBRef

solve :: C.Context cxt => cxt -> SAT.Solver -> Options -> IO ()
solve cxt solver opt = solveWBO (C.normalize cxt) solver opt

solveWBO :: C.Context cxt => cxt -> SAT.Solver -> Options -> IO ()
solveWBO cxt solver opt = do
  C.logMessage cxt $ printf "BCD2: Hardening is %s." (if optEnableHardening opt then "enabled" else "disabled")
  C.logMessage cxt $ printf "BCD2: BiasedSearch is %s." (if optEnableBiasedSearch opt then "enabled" else "disabled")

  SAT.modifyConfig solver $ \config -> config{ SAT.configEnableBackwardSubsumptionRemoval = True }

  unrelaxedRef <- newIORef $ IntSet.fromList [lit | (lit,_) <- sels]
  relaxedRef   <- newIORef IntSet.empty
  hardenedRef  <- newIORef IntSet.empty
  nsatRef   <- newIORef 1
  nunsatRef <- newIORef 1

  lastUBRef <- newIORef $ SAT.pbLinUpperBound obj

  coresRef <- newIORef []
  let getLB = do
        xs <- readIORef coresRef
        foldM (\s core -> do{ v <- getCoreLB core; return $! s + v }) 0 xs

  deductedWeightRef <- newIORef weights
  let deductWeight d core =
        modifyIORef' deductedWeightRef $ IntMap.unionWith (+) $
          IntMap.fromList [(lit, - d) | lit <- IntSet.toList (coreLits core)]
      updateLB oldLB core = do
        newLB <- getLB
        C.addLowerBound cxt newLB
        deductWeight (newLB - oldLB) core
        SAT.addPBAtLeast solver (coreCostFun core) =<< getCoreLB core -- redundant, but useful for direct search

  let loop = do
        lb <- getLB
        ub <- do
          ub1 <- atomically $ C.getSearchUpperBound cxt
          -- FIXME: The refinement should be done in Context.addSolution,
          -- for generality and to avoid duplicated computation.
          let ub2 = refineUB (map fst obj) ub1
          when (ub1 /= ub2) $ C.logMessage cxt $ printf "BCD2: refineUB: %d -> %d" ub1 ub2
          return ub2
        when (ub < lb) $ C.setFinished cxt

        fin <- atomically $ C.isFinished cxt
        unless fin $ do
               
          when (optEnableHardening opt) $ do
            deductedWeight <- readIORef deductedWeightRef
            hardened <- readIORef hardenedRef
            let lits = IntMap.keysSet (IntMap.filter (\w -> lb + w > ub) deductedWeight) `IntSet.difference` hardened
            unless (IntSet.null lits) $ do
              C.logMessage cxt $ printf "BCD2: hardening fixes %d literals" (IntSet.size lits)
              forM_ (IntSet.toList lits) $ \lit -> SAT.addClause solver [lit]
              modifyIORef unrelaxedRef (`IntSet.difference` lits)
              modifyIORef relaxedRef   (`IntSet.difference` lits)
              modifyIORef hardenedRef  (`IntSet.union` lits)
  
          ub0 <- readIORef lastUBRef  
          when (ub < ub0) $ do
            C.logMessage cxt $ printf "BCD2: updating upper bound: %d -> %d" ub0 ub
            SAT.addPBAtMost solver obj ub
            writeIORef lastUBRef ub

          cores     <- readIORef coresRef                     
          unrelaxed <- readIORef unrelaxedRef
          relaxed   <- readIORef relaxedRef
          hardened  <- readIORef hardenedRef
          nsat   <- readIORef nsatRef
          nunsat <- readIORef nunsatRef
          C.logMessage cxt $ printf "BCD2: %d <= obj <= %d" lb ub
          C.logMessage cxt $ printf "BCD2: #cores=%d, #unrelaxed=%d, #relaxed=%d, #hardened=%d" 
            (length cores) (IntSet.size unrelaxed) (IntSet.size relaxed) (IntSet.size hardened)
          C.logMessage cxt $ printf "BCD2: #sat=%d #unsat=%d bias=%d/%d" nsat nunsat nunsat (nunsat + nsat)

          lastModel <- atomically $ C.getBestModel cxt
          sels <- liftM IntMap.fromList $ forM cores $ \core -> do                            
            coreLB <- getCoreLB core
            let coreUB = SAT.pbLinUpperBound (coreCostFun core)
            if coreUB < coreLB then do
              -- Note: we have detected unsatisfiability
              C.logMessage cxt $ printf "BCD2: coreLB (%d) exceeds coreUB (%d)" coreLB coreUB
              SAT.addClause solver []
              sel <- getCoreUBAssumption core coreUB
              return (sel, (core, coreUB))
            else do
              let estimated =
                    case lastModel of
                      Nothing -> coreUB
                      Just m  ->
                        -- Since we might have added some hard constraints after obtaining @m@,
                        -- it's possible that @coreLB@ is larger than @SAT.evalPBLinSum m (coreCostFun core)@.
                        coreLB `max` SAT.evalPBLinSum m (coreCostFun core)
                  mid =
                    if optEnableBiasedSearch opt
                    then coreLB + (estimated - coreLB) * nunsat `div` (nunsat + nsat)
                    else (coreLB + estimated) `div` 2
              sel <- getCoreUBAssumption core mid
              return (sel, (core,mid))

          ret <- SAT.solveWith solver (IntMap.keys sels ++ IntSet.toList unrelaxed)

          if ret then do
            modifyIORef' nsatRef (+1)
            C.addSolution cxt =<< SAT.getModel solver
            loop
          else do
            modifyIORef' nunsatRef (+1)
            failed <- SAT.getFailedAssumptions solver

            case failed of
              [] -> C.setFinished cxt
              [sel] | Just (core,mid) <- IntMap.lookup sel sels -> do
                C.logMessage cxt $ printf "BCD2: updating lower bound of a core"
                let newCoreLB  = mid + 1
                    newCoreLB' = refineLB [weights IntMap.! lit | lit <- IntSet.toList (coreLits core)] newCoreLB
                when (newCoreLB /= newCoreLB') $ C.logMessage cxt $
                  printf "BCD2: refineLB: %d -> %d" newCoreLB newCoreLB'
                writeIORef (coreLBRef core) newCoreLB'
                SAT.addClause solver [-sel] -- Delete soft upperbound constraint(s) by fixing a selector variable
                updateLB lb core
                loop
              _ -> do
                let failed'     = IntSet.fromList failed
                    torelax     = unrelaxed `IntSet.intersection` failed'
                    intersected = [(core,mid) | (sel,(core,mid)) <- IntMap.toList sels, sel `IntSet.member` failed']
                    disjoint    = [core | (sel,(core,_)) <- IntMap.toList sels, sel `IntSet.notMember` failed']
                modifyIORef unrelaxedRef (`IntSet.difference` torelax)
                modifyIORef relaxedRef (`IntSet.union` torelax)
                delta <- do
                  xs1 <- forM intersected $ \(core,mid) -> do
                    coreLB <- getCoreLB core
                    return $ mid - coreLB + 1
                  let xs2 = [weights IntMap.! lit | lit <- IntSet.toList torelax]
                  return $! minimum (xs1 ++ xs2)
                let mergedCoreLits = IntSet.unions $ torelax : [coreLits core | (core,_) <- intersected]
                mergedCoreLB <- liftM ((delta +) . sum) $ mapM (getCoreLB . fst) intersected
                let mergedCoreLB' = refineLB [weights IntMap.! lit | lit <- IntSet.toList mergedCoreLits] mergedCoreLB
                mergedCore <- newCoreInfo mergedCoreLits mergedCoreLB'
                writeIORef coresRef (mergedCore : disjoint)
                forM_ intersected $ \(core, _) -> deleteCoreInfo solver core

                if null intersected then
                  C.logMessage cxt $ printf "BCD2: found a new core of size %d: cost of the new core is >=%d"
                    (IntSet.size torelax) mergedCoreLB'
                else
                  C.logMessage cxt $ printf "BCD2: relaxing %d and merging with %d cores into a new core of size %d: cost of the new core is >=%d"
                    (IntSet.size torelax) (length intersected) (IntSet.size mergedCoreLits) mergedCoreLB'
                when (mergedCoreLB /= mergedCoreLB') $ 
                  C.logMessage cxt $ printf "BCD2: refineLB: %d -> %d" mergedCoreLB mergedCoreLB'
                updateLB lb mergedCore
                loop

  best <- atomically $ C.getBestModel cxt
  case best of
    Nothing | optSolvingNormalFirst opt -> do
      ret <- SAT.solve solver
      if ret then
        C.addSolution cxt =<< SAT.getModel solver
      else
        C.setFinished cxt
    _ -> return ()
  loop

  where
    obj :: SAT.PBLinSum
    obj = C.getObjectiveFunction cxt

    sels :: [(SAT.Lit, Integer)]
    sels = [(-lit, w) | (w,lit) <- obj]

    weights :: SAT.LitMap Integer
    weights = IntMap.fromList sels

    coreCostFun :: CoreInfo -> SAT.PBLinSum
    coreCostFun c = [(weights IntMap.! lit, -lit) | lit <- IntSet.toList (coreLits c)]

    getCoreUBAssumption :: CoreInfo -> Integer -> IO SAT.Lit
    getCoreUBAssumption core ub = do
      m <- readIORef (coreUBSelectors core)
      case Map.splitLookup ub m of
        (_, Just sel, _) -> return sel
        (lo, Nothing, hi)  -> do
          sel <- SAT.newVar solver
          SAT.addPBAtMostSoft solver sel (coreCostFun core) ub
          writeIORef (coreUBSelectors core) (Map.insert ub sel m)
          unless (Map.null lo) $
            SAT.addClause solver [- snd (Map.findMax lo), sel] -- snd (Map.findMax lo) → sel
          unless (Map.null hi) $
            SAT.addClause solver [- sel, snd (Map.findMin hi)] -- sel → Map.findMin hi
          return sel

-- | The smallest integer greater-than or equal-to @n@ that can be obtained by summing a subset of @ws@.
-- Note that the definition is different from the one in Morgado et al.
refineLB
  :: [Integer] -- ^ @ws@
  -> Integer   -- ^ @n@
  -> Integer
refineLB ws n =
  case SubsetSum.minSubsetSum (V.fromList ws) n of
    Nothing -> sum [w | w <- ws, w > 0] + 1
    Just (obj, _) -> obj

-- | The greatest integer lesser-than or equal-to @n@ that can be obtained by summing a subset of @ws@.
refineUB
  :: [Integer] -- ^ @ws@
  -> Integer   -- ^ @n@
  -> Integer
refineUB ws n
  | n < 0 = n
  | otherwise =
      case SubsetSum.maxSubsetSum (V.fromList ws) n of
        Nothing -> sum [w | w <- ws, w < 0] - 1
        Just (obj, _) -> obj
