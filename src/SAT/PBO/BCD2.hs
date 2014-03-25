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
  }

defaultOptions :: Options
defaultOptions
  = Options
  { optLogger     = \_ -> return ()
  , optUpdateBest = \_ _ -> return ()
  , optUpdateLB   = \_ -> return ()
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
  loop (IntSet.fromList [lit | (lit,_) <- sels], IntSet.empty) [] (SAT.pbUpperBound obj) Nothing

  where
    weights :: SAT.LitMap Integer
    weights = IntMap.fromList sels

    obj :: SAT.PBLinSum
    obj = [(w,-lit) | (lit,w) <- sels]

    coreCostFun :: CoreInfo -> SAT.PBLinSum
    coreCostFun c = [(weights IntMap.! lit, -lit) | lit <- IntSet.toList (coreLits c)]

    loop :: (SAT.LitSet, SAT.LitSet) -> [CoreInfo] -> Integer -> Maybe SAT.Model -> IO (Maybe SAT.Model)
    loop (unrelaxed, relaxed) cores ub lastModel = do
      let lb = sum [coreLB info | info <- cores]
      optLogger opt $ printf "BCD2: %d <= obj <= %d" lb ub
      optLogger opt $ printf "BCD2: #cores=%d, #unrelaxed=%d, #relaxed=%d"
        (length cores) (IntSet.size unrelaxed) (IntSet.size relaxed)

      sels <- liftM IntMap.fromList $ forM cores $ \info -> do
        sel <- SAT.newVar solver
        SAT.addPBAtMostSoft solver sel (coreCostFun info) (coreMidValue info)
        return (sel, info)

      ret <- SAT.solveWith solver (IntMap.keys sels ++ IntSet.toList unrelaxed)

      if ret then do
        m <- SAT.model solver
        let val = SAT.pbEval m obj
        optUpdateBest opt m val
        let ub' = val - 1
        optLogger opt $ printf "BCD2: updating upper bound: %d -> %d" ub ub'
        SAT.addPBAtMost solver obj ub'
        let cores' = map (\info -> info{ coreEP = SAT.pbEval m (coreCostFun info) }) cores
        cont (unrelaxed, relaxed) cores' ub' (Just m)
      else do
        core <- SAT.failedAssumptions solver
        case core of
          [] -> return lastModel
          [sel] | Just info <- IntMap.lookup sel sels -> do
            let newLB  = refine [weights IntMap.! lit | lit <- IntSet.toList (coreLits info)] (coreMidValue info)
                cores' = IntMap.elems $ IntMap.insert sel info{ coreLB = newLB } sels
            optLogger opt $ printf "BCD2: updating lower bound of a core"
            cont (unrelaxed, relaxed) cores' ub lastModel
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
                                           Just m  -> SAT.pbEval m [(weights IntMap.! lit, -lit) | lit <- IntSet.toList newLits]
                              }
                cores'      = mergedCore : rest
            if null intersected then do
              optLogger opt $ printf "BCD2: found a new core of size %d" (IntSet.size torelax)              
            else do
              optLogger opt $ printf "BCD2: merging cores"
            forM_ (IntMap.keys sels) $ \sel -> SAT.addClause solver [-sel] -- delete temporary constraints
            cont (unrelaxed', relaxed') cores' ub lastModel

    cont :: (SAT.LitSet, SAT.LitSet) -> [CoreInfo] -> Integer -> Maybe SAT.Model -> IO (Maybe SAT.Model)
    cont (unrelaxed, relaxed) cores ub lastModel
      | sum [coreLB info | info <- cores] > ub = return lastModel
      | otherwise = loop (unrelaxed, relaxed) cores ub lastModel

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
