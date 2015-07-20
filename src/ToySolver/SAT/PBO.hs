{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.PBO
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
module ToySolver.SAT.PBO
  (
  -- * The @Optimizer@ type
    Optimizer
  , newOptimizer
  , newOptimizer2

  -- * Solving
  , optimize
  , addSolution

  -- * Extract results
  , getBestSolution
  , getBestValue
  , getBestModel
  , isUnsat
  , isOptimum
  , isFinished

  -- * Configulation
  , SearchStrategy (..)
  , getSearchStrategy
  , setSearchStrategy
  , defaultEnableObjFunVarsHeuristics
  , getEnableObjFunVarsHeuristics
  , setEnableObjFunVarsHeuristics
  , defaultTrialLimitConf
  , getTrialLimitConf
  , setTrialLimitConf
  , setOnUpdateBestSolution
  , setOnUpdateLowerBound
  , setLogger
  ) where

import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Data.Array.IArray
import Data.Default.Class
import Data.IORef
import qualified Data.Set as Set
import qualified Data.Map as Map
import Text.Printf
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.PBO.Context as C
import qualified ToySolver.SAT.PBO.BC as BC
import qualified ToySolver.SAT.PBO.BCD as BCD
import qualified ToySolver.SAT.PBO.BCD2 as BCD2
import qualified ToySolver.SAT.PBO.UnsatBased as UnsatBased
import qualified ToySolver.SAT.PBO.MSU4 as MSU4

-- | Optimization strategy
--
-- The default value can be obtained by 'def'.
data SearchStrategy
  = LinearSearch
  | BinarySearch
  | AdaptiveSearch
  | UnsatBased
  | MSU4
  | BC
  | BCD
  | BCD2
  deriving (Eq, Ord, Show, Enum, Bounded)

instance Default SearchStrategy where
  def = LinearSearch

data Optimizer
  = Optimizer
  { optContext :: C.SimpleContext
  , optSolver  :: SAT.Solver
  , optSearchStrategyRef :: IORef SearchStrategy
  , optEnableObjFunVarsHeuristicsRef :: IORef Bool
  , optTrialLimitConfRef :: IORef Int
  }

newOptimizer :: SAT.Solver -> SAT.PBLinSum -> IO Optimizer
newOptimizer solver obj = newOptimizer2 solver obj (\m -> SAT.evalPBLinSum m obj)

newOptimizer2 :: SAT.Solver -> SAT.PBLinSum -> (SAT.Model -> Integer) -> IO Optimizer
newOptimizer2 solver obj obj2 = do
  cxt <- C.newSimpleContext2 obj obj2
  strategyRef   <- newIORef def
  heuristicsRef <- newIORef defaultEnableObjFunVarsHeuristics
  trialLimitRef <- newIORef defaultTrialLimitConf
  return $
    Optimizer
    { optContext = cxt
    , optSolver = solver
    , optSearchStrategyRef = strategyRef
    , optEnableObjFunVarsHeuristicsRef = heuristicsRef
    , optTrialLimitConfRef = trialLimitRef
    }

optimize :: Optimizer -> IO ()
optimize opt = do
  let cxt = optContext opt
  let obj = C.getObjectiveFunction cxt
  let solver = optSolver opt

  getEnableObjFunVarsHeuristics opt >>= \b ->
    when b $ tweakParams solver obj

  m <- getBestModel opt
  case m of
    Nothing -> return ()
    Just m -> do
      forM_ (assocs m) $ \(v, val) -> do
        SAT.setVarPolarity solver v val

  strategy <- getSearchStrategy opt
  case strategy of
    UnsatBased -> UnsatBased.solve cxt solver
    MSU4 -> MSU4.solve cxt solver
    BC   -> BC.solve cxt solver
    BCD  -> BCD.solve cxt solver
    BCD2 -> do
      let opt2 = def
      BCD2.solve cxt solver opt2
    _ -> do
      SAT.setEnableBackwardSubsumptionRemoval solver True

      join $ atomically $ do
        ret <- C.getBestValue cxt
        case ret of
          Just _ -> return $ return ()
          Nothing -> return $ do
            result <- SAT.solve solver
            if not result then
              C.setFinished cxt
            else do
              m <- SAT.getModel solver
              C.addSolution cxt m

      join $ atomically $ do
        ret <- C.getBestValue cxt
        case ret of
          Nothing  -> return $ return ()
          Just val -> return $ do
            let ub = val - 1
            SAT.addPBAtMost solver obj ub

      case strategy of
        LinearSearch   -> linSearch cxt solver
        BinarySearch   -> binSearch cxt solver
        AdaptiveSearch -> do
          lim <- getTrialLimitConf opt
          adaptiveSearch cxt solver lim
        _              -> error "ToySolver.SAT.PBO.minimize: should not happen"  

getSearchStrategy :: Optimizer -> IO SearchStrategy
getSearchStrategy opt = readIORef (optSearchStrategyRef opt)

setSearchStrategy :: Optimizer -> SearchStrategy -> IO ()
setSearchStrategy opt val = writeIORef (optSearchStrategyRef opt) val

defaultEnableObjFunVarsHeuristics :: Bool
defaultEnableObjFunVarsHeuristics = False

getEnableObjFunVarsHeuristics :: Optimizer -> IO Bool
getEnableObjFunVarsHeuristics opt = readIORef (optEnableObjFunVarsHeuristicsRef opt)

setEnableObjFunVarsHeuristics :: Optimizer -> Bool -> IO ()
setEnableObjFunVarsHeuristics opt val = writeIORef (optEnableObjFunVarsHeuristicsRef opt) val

defaultTrialLimitConf :: Int
defaultTrialLimitConf = 1000

getTrialLimitConf :: Optimizer -> IO Int
getTrialLimitConf opt = readIORef (optTrialLimitConfRef opt)

setTrialLimitConf :: Optimizer -> Int -> IO ()
setTrialLimitConf opt val = writeIORef (optTrialLimitConfRef opt) val


setOnUpdateBestSolution :: Optimizer -> (SAT.Model -> Integer -> IO ()) -> IO ()
setOnUpdateBestSolution opt cb = C.setOnUpdateBestSolution (optContext opt) cb

setOnUpdateLowerBound :: Optimizer -> (Integer -> IO ()) -> IO ()
setOnUpdateLowerBound opt cb = C.setOnUpdateLowerBound (optContext opt) cb

setLogger :: Optimizer -> (String -> IO ()) -> IO ()
setLogger opt cb = C.setLogger (optContext opt) cb


addSolution :: Optimizer -> SAT.Model -> IO ()
addSolution opt m = C.addSolution (optContext opt) m

getBestSolution :: Optimizer -> IO (Maybe (SAT.Model, Integer))
getBestSolution opt = atomically $ C.getBestSolution (optContext opt)

getBestValue :: Optimizer -> IO (Maybe Integer)
getBestValue opt = atomically $ C.getBestValue (optContext opt)

getBestModel :: Optimizer -> IO (Maybe SAT.Model)
getBestModel opt = atomically $ C.getBestModel (optContext opt)

isUnsat :: Optimizer -> IO Bool
isUnsat opt = atomically $ C.isUnsat (optContext opt)

isOptimum :: Optimizer -> IO Bool
isOptimum opt = atomically $ C.isOptimum (optContext opt)

isFinished :: Optimizer -> IO Bool
isFinished opt = atomically $ C.isFinished (optContext opt)


linSearch :: C.Context cxt => cxt -> SAT.Solver -> IO ()
linSearch cxt solver = loop
  where
    obj = C.getObjectiveFunction cxt

    loop :: IO ()
    loop = do
      result <- SAT.solve solver
      if result then do
        m <- SAT.getModel solver        
        let val = C.evalObjectiveFunction cxt m
        let ub = val - 1
        C.addSolution cxt m
        SAT.addPBAtMost solver obj ub
        loop
      else do
        C.setFinished cxt
        return ()

binSearch :: C.Context cxt => cxt -> SAT.Solver -> IO ()
binSearch cxt solver = loop
  where
    obj = C.getObjectiveFunction cxt

    loop :: IO ()
    loop = join $ atomically $ do
      ub <- C.getSearchUpperBound cxt
      lb <- C.getLowerBound cxt
      if ub < lb then do
        return $ C.setFinished cxt
      else
        return $ do
          let mid = (lb + ub) `div` 2
          C.logMessage cxt $ printf "Binary Search: %d <= obj <= %d; guessing obj <= %d" lb ub mid
          sel <- SAT.newVar solver
          SAT.addPBAtMostSoft solver sel obj mid
          ret <- SAT.solveWith solver [sel]
          if ret then do
            m <- SAT.getModel solver
            let v = C.evalObjectiveFunction cxt m
            let ub' = v - 1
            C.logMessage cxt $ printf "Binary Search: updating upper bound: %d -> %d" ub ub'
            C.addSolution cxt m
            -- old upper bound constraints will be removed by backward subsumption removal
            SAT.addClause solver [sel]
            SAT.addPBAtMost solver obj ub'
            loop
          else do
            -- deleting temporary constraint
            SAT.addClause solver [-sel]
            let lb' = mid + 1
            C.logMessage cxt $ printf "Binary Search: updating lower bound: %d -> %d" lb lb'
            C.addLowerBound cxt lb'
            SAT.addPBAtLeast solver obj lb'
            loop

-- adaptive search strategy from pbct-0.1.3 <http://www.residual.se/pbct/>
adaptiveSearch :: C.Context cxt => cxt -> SAT.Solver -> Int -> IO ()
adaptiveSearch cxt solver trialLimitConf = loop 0
  where
    obj = C.getObjectiveFunction cxt

    loop :: Rational -> IO ()
    loop fraction = join $ atomically $ do
      ub <- C.getSearchUpperBound cxt
      lb <- C.getLowerBound cxt
      if ub < lb then
        return $ C.setFinished cxt
      else
        return $ do
          let interval = ub - lb
              mid = ub - floor (fromIntegral interval * fraction)
          if ub == mid then do
            C.logMessage cxt $ printf "Adaptive Search: %d <= obj <= %d" lb ub
            result <- SAT.solve solver
            if result then do
              m <- SAT.getModel solver
              let v = C.evalObjectiveFunction cxt m
              let ub' = v - 1
              C.addSolution cxt m
              SAT.addPBAtMost solver obj ub'
              let fraction' = min 0.5 (fraction + 0.1)
              loop fraction'
            else
              C.setFinished cxt
          else do
            C.logMessage cxt $ printf "Adaptive Search: %d <= obj <= %d; guessing obj <= %d" lb ub mid
            sel <- SAT.newVar solver
            SAT.addPBAtMostSoft solver sel obj mid
            SAT.setConfBudget solver $ Just trialLimitConf
            ret' <- try $ SAT.solveWith solver [sel]
            SAT.setConfBudget solver Nothing
            case ret' of
              Left SAT.BudgetExceeded -> do
                let fraction' = max 0 (fraction - 0.05)
                loop fraction'
              Right ret -> do
                let fraction' = min 0.5 (fraction + 0.1)
                if ret then do
                  m <- SAT.getModel solver
                  let v = C.evalObjectiveFunction cxt m
                  let ub' = v - 1
                  C.logMessage cxt $ printf "Adaptive Search: updating upper bound: %d -> %d" ub ub'
                  C.addSolution cxt m
                  -- old upper bound constraints will be removed by backward subsumption removal
                  SAT.addClause solver [sel]
                  SAT.addPBAtMost solver obj ub'
                  loop fraction'
                else do
                  -- deleting temporary constraint
                  SAT.addClause solver [-sel]
                  let lb' = mid + 1
                  C.logMessage cxt $ printf "Adaptive Search: updating lower bound: %d -> %d" lb lb'
                  C.addLowerBound cxt lb'
                  SAT.addPBAtLeast solver obj lb'
                  loop fraction'

tweakParams :: SAT.Solver -> SAT.PBLinSum -> IO ()
tweakParams solver obj = do
  forM_ obj $ \(c,l) -> do
    let p = if c > 0 then not (SAT.litPolarity l) else SAT.litPolarity l
    SAT.setVarPolarity solver (SAT.litVar l) p
  let cs = Set.fromList [abs c | (c,_) <- obj]
      ws = Map.fromAscList $ zip (Set.toAscList cs) [1..]
  forM_ obj $ \(c,l) -> do
    let w = ws Map.! abs c
    replicateM w $ SAT.varBumpActivity solver (SAT.litVar l)
