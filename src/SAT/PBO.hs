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
import qualified Data.Set as Set
import qualified Data.Map as Map
import Text.Printf
import SAT
import SAT.Types
import qualified SAT.PBO.BC as BC
import qualified SAT.PBO.BCD as BCD
import qualified SAT.PBO.BCD2 as BCD2
import qualified SAT.PBO.UnsatBased as UnsatBased
import qualified SAT.PBO.MSU4 as MSU4

data SearchStrategy
  = LinearSearch
  | BinarySearch
  | AdaptiveSearch
  | UnsatBased
  | MSU4
  | BC
  | BCD
  | BCD2

data Options
  = Options
  { optLogger               :: String -> IO ()
  , optUpdateBest           :: Model -> Integer -> IO ()
  , optUpdateLB             :: Integer -> IO ()
  , optObjFunVarsHeuristics :: Bool
  , optSearchStrategy       :: SearchStrategy
  , optTrialLimitConf       :: Int
  , optInitialModel         :: Maybe SAT.Model
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
  , optInitialModel         = Nothing
  }

minimize :: Solver -> PBLinSum -> Options -> IO (Maybe Model)
minimize solver obj opt = do
  when (optObjFunVarsHeuristics opt) $ tweakParams solver obj

  updateLB (pbLowerBound obj)
  case optInitialModel opt of
    Just m -> do
      let val = evalPBSum m obj
      updateBest m val
      addPBAtMost solver obj (val - 1)
    Nothing -> do
      return ()

  case optSearchStrategy opt of
    UnsatBased -> do
      let opt2 = UnsatBased.defaultOptions
                 { UnsatBased.optLogger     = optLogger opt
                 , UnsatBased.optUpdateBest = optUpdateBest opt
                 , UnsatBased.optUpdateLB   = optUpdateLB opt
                 }
      UnsatBased.solve solver obj opt2
    MSU4 -> do
      let opt2 = MSU4.defaultOptions
                 { MSU4.optLogger     = optLogger opt
                 , MSU4.optUpdateBest = optUpdateBest opt
                 , MSU4.optUpdateLB   = optUpdateLB opt
                 , MSU4.optInitialModel = optInitialModel opt
                 }
      MSU4.solve solver obj opt2
    BC -> do
      let opt2 = BC.defaultOptions
                 { BC.optLogger     = optLogger opt
                 , BC.optUpdateBest = optUpdateBest opt
                 , BC.optUpdateLB   = optUpdateLB opt
                 , BC.optInitialModel = optInitialModel opt
                 }
      BC.solve solver obj opt2
    BCD -> do
      let opt2 = BCD.defaultOptions
                 { BCD.optLogger     = optLogger opt
                 , BCD.optUpdateBest = optUpdateBest opt
                 , BCD.optUpdateLB   = optUpdateLB opt
                 , BCD.optInitialModel = optInitialModel opt
                 }
      BCD.solve solver obj opt2
    BCD2 -> do
      let opt2 = BCD2.defaultOptions
                 { BCD2.optLogger     = optLogger opt
                 , BCD2.optUpdateBest = optUpdateBest opt
                 , BCD2.optUpdateLB   = optUpdateLB opt
                 , BCD2.optInitialModel = optInitialModel opt
                 }
      BCD2.solve solver obj opt2
    _ -> do
      SAT.setEnableBackwardSubsumptionRemoval solver True
      let f m0 = case optSearchStrategy opt of
                   LinearSearch   -> liftM Just $ linSearch m0
                   BinarySearch   -> liftM Just $ binSearch m0
                   AdaptiveSearch -> liftM Just $ adaptiveSearch m0
                   _              -> error "SAT.PBO.minimize: should not happen"
      case optInitialModel opt of
        Just m0 -> f m0
        Nothing -> do
          result <- solve solver
          if not result then
            return Nothing
          else do
            m0 <- model solver
            f m0

  where
    logIO :: String -> IO ()
    logIO = optLogger opt

    updateBest :: Model -> Integer -> IO ()
    updateBest = optUpdateBest opt

    updateLB :: Integer -> IO ()
    updateLB = optUpdateLB opt

    linSearch :: Model -> IO Model
    linSearch m0 = do
      result <- solve solver
      if result then do
        m <- model solver
        let v = evalPBSum m obj
        updateBest m v
        addPBAtMost solver obj (v - 1)
        linSearch m
      else
        return m0

    binSearch :: Model -> IO Model
    binSearch m0 = do
      let ub0 = evalPBSum m0 obj - 1
          lb0 = pbLowerBound obj
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
            let v = evalPBSum m2 obj
            updateBest m2 v
            let ub' = v - 1
            logIO $ printf "Binary Search: updating upper bound: %d -> %d" ub ub'
            -- old upper bound constraints will be removed by backward subsumption removal
            addClause solver [sel]
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
    adaptiveSearch :: Model -> IO Model
    adaptiveSearch m0 = do
      let ub0 = evalPBSum m0 obj - 1
          lb0 = pbLowerBound obj
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
              let v = evalPBSum m2 obj
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
                  let v = evalPBSum m2 obj
                  updateBest m2 v
                  let ub' = v - 1
                  logIO $ printf "Adaptive Search: updating upper bound: %d -> %d" ub ub'
                  -- old upper bound constraints will be removed by backward subsumption removal
                  addClause solver [sel]
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

tweakParams :: Solver -> PBLinSum -> IO ()
tweakParams solver obj = do
  forM_ obj $ \(c,l) -> do
    let p = if c > 0 then not (litPolarity l) else litPolarity l
    setVarPolarity solver (litVar l) p
  let cs = Set.fromList [abs c | (c,_) <- obj]
      ws = Map.fromAscList $ zip (Set.toAscList cs) [1..]
  forM_ obj $ \(c,l) -> do
    let w = ws Map.! abs c
    replicateM w $ varBumpActivity solver (litVar l)
