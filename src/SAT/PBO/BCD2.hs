{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  SAT.PBO.BCD2
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
--   <http://dx.doi.org/10.1007/978-3-642-31612-8_22>
--   <http://ulir.ul.ie/handle/10344/2771>
-- 
-----------------------------------------------------------------------------
module SAT.PBO.BCD2
  ( Options (..)
  , defaultOptions
  , solve
  ) where

import qualified Algorithm.Knapsack as Knapsack
import Control.Exception
import Control.Monad
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
  , optEnableHardening :: Bool
  , optSolvingNormalFirst :: Bool
  }

defaultOptions :: Options
defaultOptions
  = Options
  { optLogger     = \_ -> return ()
  , optUpdateBest = \_ _ -> return ()
  , optUpdateLB   = \_ -> return ()
  , optInitialModel = Nothing
  , optEnableHardening = True
  , optSolvingNormalFirst = True
  }

data CoreInfo
  = CoreInfo
  { coreLits :: SAT.LitSet
  , coreLB   :: !Integer
  , coreEP   :: !Integer
  }

coreMidValue :: CoreInfo -> Integer
coreMidValue c = (coreLB c + coreEP c) `div` 2

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
  let unrelaxed = IntSet.fromList [lit | (lit,_) <- sels]
      relaxed   = IntSet.empty
      hardened  = IntSet.empty
  case optInitialModel opt of
    Just m -> do
      loop (unrelaxed, relaxed, hardened) weights [] (SAT.evalPBSum m obj - 1) (Just m)
    Nothing
      | optSolvingNormalFirst opt -> do
          ret <- SAT.solve solver
          if ret then do
            m <- SAT.model solver
            let val = SAT.evalPBSum m obj
            optUpdateBest opt m val
            let ub' = val - 1
            optLogger opt $ printf "BCD2: updating upper bound: %d -> %d" (SAT.pbUpperBound obj) ub'
            SAT.addPBAtMost solver obj ub'
            loop (unrelaxed, relaxed, hardened) weights [] ub' (Just m)
          else
            return Nothing
      | otherwise -> do
          loop (unrelaxed, relaxed, hardened) weights [] (SAT.pbUpperBound obj) Nothing
  where
    weights :: SAT.LitMap Integer
    weights = IntMap.fromList sels

    obj :: SAT.PBLinSum
    obj = [(w,-lit) | (lit,w) <- sels]

    coreCostFun :: CoreInfo -> SAT.PBLinSum
    coreCostFun c = [(weights IntMap.! lit, -lit) | lit <- IntSet.toList (coreLits c)]

    computeLB :: [CoreInfo] -> Integer
    computeLB cores = sum [coreLB info | info <- cores]

    loop :: (SAT.LitSet, SAT.LitSet, SAT.LitSet) -> SAT.LitMap Integer -> [CoreInfo] -> Integer -> Maybe SAT.Model -> IO (Maybe SAT.Model)
    loop (unrelaxed, relaxed, hardened) deductedWeight cores ub lastModel = do
      let lb = computeLB cores
      optLogger opt $ printf "BCD2: %d <= obj <= %d" lb ub
      optLogger opt $ printf "BCD2: #cores=%d, #unrelaxed=%d, #relaxed=%d, #hardened=%d" 
        (length cores) (IntSet.size unrelaxed) (IntSet.size relaxed) (IntSet.size hardened)

      sels <- liftM IntMap.fromList $ forM cores $ \info -> do
        sel <- SAT.newVar solver
        SAT.addPBAtMostSoft solver sel (coreCostFun info) (coreMidValue info)
        return (sel, info)

      ret <- SAT.solveWith solver (IntMap.keys sels ++ IntSet.toList unrelaxed)

      if ret then do
        m <- SAT.model solver
        let val = SAT.evalPBSum m obj
        optUpdateBest opt m val
        let ub' = val - 1
        optLogger opt $ printf "BCD2: updating upper bound: %d -> %d" ub ub'
        SAT.addPBAtMost solver obj ub'
        let cores' = map (\info -> info{ coreEP = SAT.evalPBSum m (coreCostFun info) }) cores
        cont (unrelaxed, relaxed, hardened) deductedWeight cores' ub' (Just m)
      else do
        core <- SAT.failedAssumptions solver
        case core of
          [] -> return lastModel
          [sel] | Just info <- IntMap.lookup sel sels -> do
            let newLB  = refine [weights IntMap.! lit | lit <- IntSet.toList (coreLits info)] (coreMidValue info)
                info'  = info{ coreLB = newLB }
                cores' = IntMap.elems $ IntMap.insert sel info' sels
                lb'    = computeLB cores'
                deductedWeight' = IntMap.unionWith (+) deductedWeight (IntMap.fromList [(lit, - d)  | let d = lb' - lb, d /= 0, lit <- IntSet.toList (coreLits info)])
            optLogger opt $ printf "BCD2: updating lower bound of a core"
            SAT.addPBAtLeast solver (coreCostFun info') (coreLB info') -- redundant, but useful for direct search
            cont (unrelaxed, relaxed, hardened) deductedWeight' cores' ub lastModel
          _ -> do
            let coreSet     = IntSet.fromList core
                torelax     = unrelaxed `IntSet.intersection` coreSet
                unrelaxed'  = unrelaxed `IntSet.difference` torelax
                relaxed'    = relaxed `IntSet.union` torelax
                intersected = [info | (sel,info) <- IntMap.toList sels, sel `IntSet.member` coreSet]
                rest        = [info | (sel,info) <- IntMap.toList sels, sel `IntSet.notMember` coreSet]
                delta       = minimum $ [coreMidValue info - coreLB info + 1 | info <- intersected] ++ 
                                        [weights IntMap.! lit | lit <- IntSet.toList torelax]
                newLits     = IntSet.unions $ torelax : [coreLits info | info <- intersected]
                mergedCore  = CoreInfo
                              { coreLits = newLits
                              , coreLB = refine [weights IntMap.! lit | lit <- IntSet.toList relaxed'] (sum [coreLB info | info <- intersected] + delta - 1)
                              , coreEP = case lastModel of
                                           Nothing -> sum [weights IntMap.! lit | lit <- IntSet.toList newLits]
                                           Just m  -> SAT.evalPBSum m [(weights IntMap.! lit, -lit) | lit <- IntSet.toList newLits]
                              }
                cores'      = mergedCore : rest
                lb'         = computeLB cores'
                deductedWeight' = IntMap.unionWith (+) deductedWeight (IntMap.fromList [(lit, - d)  | let d = lb' - lb, d /= 0, lit <- IntSet.toList newLits])
            if null intersected then do
              optLogger opt $ printf "BCD2: found a new core of size %d" (IntSet.size torelax)              
            else do
              optLogger opt $ printf "BCD2: merging cores"
            SAT.addPBAtLeast solver (coreCostFun mergedCore) (coreLB mergedCore) -- redundant, but useful for direct search
            forM_ (IntMap.keys sels) $ \sel -> SAT.addClause solver [-sel] -- delete temporary constraints
            cont (unrelaxed', relaxed', hardened) deductedWeight' cores' ub lastModel

    cont :: (SAT.LitSet, SAT.LitSet, SAT.LitSet) -> SAT.LitMap Integer -> [CoreInfo] -> Integer -> Maybe SAT.Model -> IO (Maybe SAT.Model)
    cont (unrelaxed, relaxed, hardened) deductedWeight cores ub lastModel
      | lb > ub = return lastModel
      | optEnableHardening opt = do
          let lits = IntMap.keysSet $ IntMap.filter (\w -> lb + w > ub) deductedWeight
          forM_ (IntSet.toList lits) $ \lit -> SAT.addClause solver [lit]
          let unrelaxed' = unrelaxed `IntSet.difference` lits
              relaxed'   = relaxed   `IntSet.difference` lits
              hardened'  = hardened  `IntSet.union` lits
              cores'     = map (\core -> core{ coreLits = coreLits core `IntSet.difference` lits }) cores
          loop (unrelaxed', relaxed', hardened') deductedWeight cores' ub lastModel
      | otherwise = 
          loop (unrelaxed, relaxed, hardened) deductedWeight cores ub lastModel
      where
        lb = computeLB cores

-- | The smallest integer greater than @n@ that can be obtained by summing a subset of @ws@.
refine
  :: [Integer] -- ^ @ws@
  -> Integer   -- ^ @n@
  -> Integer
refine ws n = n+1
{-
refine ws n = assert (n+1 <= result) $ result
  where
    sum_ws = sum ws
    (v,_,_) = Knapsack.solve [(fromInteger w, fromInteger w) | w <- ws] (fromInteger (sum_ws - n - 1))
    result = sum_ws - floor v
-}
{-
minimize Σ wi xi = Σ wi (1 - ¬xi) = Σ wi - (Σ wi ¬xi)
subject to Σ wi xi > n

maximize Σ wi ¬xi
subject to Σ wi ¬xi ≤ (Σ wi) - n - 1

Σ wi xi > n
Σ wi (1 - ¬xi) > n
(Σ wi) - (Σ wi ¬xi) > n
(Σ wi ¬xi) < (Σ wi) - n
(Σ wi ¬xi) ≤ (Σ wi) - n - 1
-}
