{-# LANGUAGE DoAndIfThenElse #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  SAT.PBO
-- Copyright   :  (c) Masahiro Sakai 2012-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Pseudo-Boolean Optimization (PBO) Solver
--
-----------------------------------------------------------------------------
module SAT.PBO where

import Control.Exception
import Control.Monad
import Data.List
import Data.Ord
import Text.Printf
import SAT
import SAT.Types
import qualified SAT.PBO.UnsatBased as UnsatBased

data SearchStrategy
  = LinearSearch
  | BinarySearch
  | AdaptiveSearch
  | UnsatBased

data Options
  = Options
  { optLogger               :: String -> IO ()
  , optUpdateBest           :: Model -> Integer -> IO ()
  , optUpdateLB             :: Integer -> IO ()
  , optObjFunVarsHeuristics :: Bool
  , optSearchStrategy       :: SearchStrategy
  , optTrialLimitConf       :: Int
  }

defaultOptions :: Options
defaultOptions
  = Options
  { optLogger               = \_ -> return ()
  , optUpdateBest           = \_ _ -> return ()
  , optUpdateLB             = \_ -> return ()
  , optObjFunVarsHeuristics = True
  , optSearchStrategy       = LinearSearch
  , optTrialLimitConf       = 1000
  }

minimize :: Solver -> [(Integer, Lit)] -> Options -> IO (Maybe Model)
minimize solver obj opt = do
  when (optObjFunVarsHeuristics opt) $ tweakParams solver obj

  case optSearchStrategy opt of
    UnsatBased -> do
      let opt2 = UnsatBased.defaultOptions
                 { UnsatBased.optLogger     = optLogger opt
                 , UnsatBased.optUpdateBest = optUpdateBest opt
                 , UnsatBased.optUpdateLB   = optUpdateLB opt
                 }
      UnsatBased.solve solver obj opt2
    _ -> do
      updateLB (pbLowerBound obj)
      result <- solve solver
      if not result then
        return Nothing
      else
        case optSearchStrategy opt of
          LinearSearch   -> liftM Just linSearch
          BinarySearch   -> liftM Just binSearch
          AdaptiveSearch -> liftM Just adaptiveSearch
          _              -> error "SAT.PBO.minimize: should not happen"

  where
    logIO :: String -> IO ()
    logIO = optLogger opt

    updateBest :: Model -> Integer -> IO ()
    updateBest = optUpdateBest opt

    updateLB :: Integer -> IO ()
    updateLB = optUpdateLB opt

    linSearch :: IO Model
    linSearch = do
      m <- model solver
      let v = pbEval m obj
      updateBest m v
      addPBAtMost solver obj (v - 1)
      result <- solve solver
      if result
        then linSearch
        else return m

    binSearch :: IO Model
    binSearch = do
      m0 <- model solver
      let v0 = pbEval m0 obj
      updateBest m0 v0
      let ub0 = v0 - 1
          lb0 = pbLowerBound obj
      addPBAtMost solver obj ub0
      loop lb0 ub0 m0
      where
        loop lb ub m | ub < lb = return m
        loop lb ub m = do
          let mid = (lb + ub) `div` 2
          logIO $ printf "Binary Search: %d <= obj <= %d; guessing obj <= %d" lb ub mid
          sel <- newVar solver
          addPBAtMostSoft solver sel obj mid
          ret <- solveWith solver [sel]
          if ret then do
            m2 <- model solver
            let v = pbEval m2 obj
            updateBest m2 v
            -- deleting temporary constraint
            -- ただし、これに依存した補題を活かすためには残したほうが良い?
            addClause solver [-sel]
            let ub' = v - 1
            logIO $ printf "Binary Search: updating upper bound: %d -> %d" ub ub'
            addPBAtMost solver obj ub'
            loop lb ub' m2
          else do
            -- deleting temporary constraint
            addClause solver [-sel]
            let lb' = mid + 1
            updateLB lb'
            logIO $ printf "Binary Search: updating lower bound: %d -> %d" lb lb'
            addPBAtLeast solver obj lb'
            loop lb' ub m

    -- adaptive search strategy from pbct-0.1.3 <http://www.residual.se/pbct/>
    adaptiveSearch :: IO Model
    adaptiveSearch = do
      m0 <- model solver
      let v0 = pbEval m0 obj
      updateBest m0 v0
      let ub0 = v0 - 1
          lb0 = pbLowerBound obj
      addPBAtMost solver obj ub0
      loop lb0 ub0 (0::Rational) m0
      where
        loop lb ub _ m | ub < lb = return m
        loop lb ub fraction m = do
          let interval = ub - lb
              mid = ub - floor (fromIntegral interval * fraction)
          if ub == mid then do
            logIO $ printf "Adaptive Search: %d <= obj <= %d" lb ub
            result <- solve solver
            if result then do
              m2 <- model solver
              let v = pbEval m2 obj
              updateBest m2 v
              let ub'   = v - 1
                  fraction' = min 0.5 (fraction + 0.1)
              loop lb ub' fraction' m2
            else
              return m
          else do
            logIO $ printf "Adaptive Search: %d <= obj <= %d; guessing obj <= %d" lb ub mid
            sel <- newVar solver
            addPBAtMostSoft solver sel obj mid
            setConfBudget solver $ Just (optTrialLimitConf opt)
            ret' <- try $ solveWith solver [sel]
            setConfBudget solver Nothing
            case ret' of
              Left BudgetExceeded -> do
                let fraction' = max 0 (fraction - 0.05)
                loop lb ub fraction' m
              Right ret -> do
                let fraction' = min 0.5 (fraction + 0.1)
                if ret then do
                  m2 <- model solver
                  let v = pbEval m2 obj
                  updateBest m2 v
                  -- deleting temporary constraint
                  -- ただし、これに依存した補題を活かすためには残したほうが良い?
                  addClause solver [-sel]
                  let ub' = v - 1
                  logIO $ printf "Adaptive Search: updating upper bound: %d -> %d" ub ub'
                  addPBAtMost solver obj ub'
                  loop lb ub' fraction' m2
                else do
                  -- deleting temporary constraint
                  addClause solver [-sel]
                  let lb' = mid + 1
                  updateLB lb'
                  logIO $ printf "Adaptive Search: updating lower bound: %d -> %d" lb lb'
                  addPBAtLeast solver obj lb'
                  loop lb' ub fraction' m

tweakParams :: Solver -> [(Integer, Lit)] -> IO ()
tweakParams solver obj = do
  forM_ obj $ \(c,l) -> do
    let p = if c > 0 then not (litPolarity l) else litPolarity l
    setVarPolarity solver (litVar l) p
  forM_ (zip [1..] (map snd (sortBy (comparing fst) [(abs c, l) | (c,l) <- obj]))) $ \(n,l) -> do
    replicateM n $ varBumpActivity solver (litVar l)
