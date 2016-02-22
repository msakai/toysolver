{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables, BangPatterns, TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.MessagePassing.SurveyPropagation
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, BangPatterns, TypeFamilies)
--
-- References:
--
-- * Alfredo Braunstein, Marc Mézard and Riccardo Zecchina.
--   Survey Propagation: An Algorithm for Satisfiability,
--   <http://arxiv.org/abs/cs/0212002>

-- * Corrie Scalisi. Visualizing Survey Propagation in 3-SAT Factor Graphs,
--   <http://classes.soe.ucsc.edu/cmps290c/Winter06/proj/corriereport.pdf>.
--
-----------------------------------------------------------------------------
module ToySolver.SAT.MessagePassing.SurveyPropagation
  (
  -- * The Solver type
    Solver
  , newSolver

  -- * Problem information
  , getNVars
  , getNConstraints

  -- * Parameters
  , getTolerance
  , setTolerance
  , getIterationLimit
  , setIterationLimit
  , getNThreads
  , setNThreads

  -- * Computing marginal distributions
  , initializeRandom
  , propagate
  , getVarProb

  -- * Solving
  , findLargestBiasLit
  , fixLit
  , unfixLit
  , solve

  -- * Debugging
  , printInfo
  ) where

import Control.Applicative
import Control.Concurrent
import Control.Concurrent.STM
import Control.Exception
import Control.Loop
import Control.Monad
import qualified Data.Array.IArray as A
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.IORef
import Data.Maybe (fromJust)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as VM
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import Data.Vector.Generic ((!))
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Generic.Mutable as VGM
import qualified System.Random.MWC as Rand

import qualified ToySolver.SAT.Types as SAT

type ClauseIndex = Int
type EdgeIndex   = Int

data Solver
  = Solver
  { svVarEdges :: !(V.Vector [EdgeIndex])
  , svVarProbT :: !(VUM.IOVector Double)
  , svVarProbF :: !(VUM.IOVector Double)
  , svVarFixed :: !(VM.IOVector (Maybe Bool))

  , svClauseEdges :: !(V.Vector [EdgeIndex])
  , svClauseWeight :: !(VU.Vector Double)

  , svEdgeLit    :: !(VU.Vector SAT.Lit) -- i
  , svEdgeClause :: !(VU.Vector ClauseIndex) -- a
  , svEdgeSurvey :: !(VUM.IOVector Double) -- η_{a → i}
  , svEdgeProbS  :: !(VUM.IOVector Double) -- Π^s_{i → a}
  , svEdgeProbU  :: !(VUM.IOVector Double) -- Π^u_{i → a}
  , svEdgeProb0  :: !(VUM.IOVector Double) -- Π^0_{i → a}

  , svTolRef :: !(IORef Double)
  , svIterLimRef :: !(IORef (Maybe Int))
  , svNThreadsRef :: !(IORef Int)
  }

newSolver :: Int -> [(Double, SAT.Clause)] -> IO Solver
newSolver nv clauses = do
  let num_clauses = length clauses
      num_edges = sum [length c | (_,c) <- clauses]

  varEdgesRef <- newIORef IntMap.empty
  clauseEdgesM <- VGM.new num_clauses

  (edgeLitM :: VUM.IOVector SAT.Lit) <- VGM.new num_edges
  (edgeClauseM :: VUM.IOVector ClauseIndex) <- VGM.new num_edges

  ref <- newIORef 0
  forM_ (zip [0..] clauses) $ \(i,(_,c)) -> do
    es <- forM c $ \lit -> do
      e <- readIORef ref
      modifyIORef' ref (+1)
      modifyIORef' varEdgesRef (IntMap.insertWith IntSet.union (abs lit) (IntSet.singleton e))
      VGM.write edgeLitM e lit
      VGM.write edgeClauseM e i
      return e
    VGM.write clauseEdgesM i es

  varEdges <- readIORef varEdgesRef
  clauseEdges <- VG.unsafeFreeze clauseEdgesM

  edgeLit     <- VG.unsafeFreeze edgeLitM
  edgeClause  <- VG.unsafeFreeze edgeClauseM

  -- Initialize all surveys with non-zero values.
  -- If we initialize to zero, following trivial solution exists:
  -- * η_{a→i} = 0 for all i and a.
  -- * Π^0_{i→a} = 1, Π^u_{i→a} = Π^s_{i→a} = 0 for all i and a,
  -- * \^{Π}^{0}_i = 1, \^{Π}^{+}_i = \^{Π}^{-}_i = 0
  edgeSurvey  <- VGM.replicate num_edges 0.5
  edgeProbS   <- VGM.new num_edges
  edgeProbU   <- VGM.new num_edges
  edgeProb0   <- VGM.new num_edges

  varFixed <- VGM.replicate nv Nothing
  varProbT <- VGM.new nv
  varProbF <- VGM.new nv

  tolRef <- newIORef 0.01
  maxIterRef <- newIORef (Just 1000)
  nthreadsRef <- newIORef 1

  let solver = Solver
        { svVarEdges    = VG.generate nv $ \i ->
            case IntMap.lookup (i+1) varEdges of
              Nothing -> []
              Just es -> IntSet.toList es
        , svVarProbT = varProbT
        , svVarProbF = varProbF
        , svVarFixed = varFixed

        , svClauseEdges = clauseEdges
        , svClauseWeight = VG.fromListN (VG.length clauseEdges) (map fst clauses)

        , svEdgeLit     = edgeLit
        , svEdgeClause  = edgeClause
        , svEdgeSurvey  = edgeSurvey
        , svEdgeProbS   = edgeProbS
        , svEdgeProbU   = edgeProbU
        , svEdgeProb0   = edgeProb0

        , svTolRef = tolRef
        , svIterLimRef = maxIterRef
        , svNThreadsRef = nthreadsRef
        }

  return solver

initializeRandom :: Solver -> Rand.GenIO -> IO ()
initializeRandom solver gen = do
  n <- getNEdges solver
  numLoop 0 (n-1) $ \e -> do
    VGM.write (svEdgeSurvey solver) e =<< Rand.uniformR (0.05,0.95) gen -- (0.05, 0.95]

-- | number of variables of the problem.
getNVars :: Solver -> IO Int
getNVars solver = return $ VG.length (svVarEdges solver)

-- | number of constraints of the problem.
getNConstraints :: Solver -> IO Int
getNConstraints solver = return $ VG.length (svClauseEdges solver)

-- | number of edges of the factor graph
getNEdges :: Solver -> IO Int
getNEdges solver = return $ VG.length (svEdgeLit solver)

getTolerance :: Solver -> IO Double
getTolerance solver = readIORef (svTolRef solver)

setTolerance :: Solver -> Double -> IO ()
setTolerance solver !tol = writeIORef (svTolRef solver) tol

getIterationLimit :: Solver -> IO (Maybe Int)
getIterationLimit solver = readIORef (svIterLimRef solver)

setIterationLimit :: Solver -> Maybe Int -> IO ()
setIterationLimit solver val = writeIORef (svIterLimRef solver) val

getNThreads :: Solver -> IO Int
getNThreads solver = readIORef (svNThreadsRef solver)

setNThreads :: Solver -> Int -> IO ()
setNThreads solver val = writeIORef (svNThreadsRef solver) val

propagate :: Solver -> IO Bool
propagate solver = do
  nthreads <- getNThreads solver
  if nthreads > 1 then
    propagateMT solver nthreads
  else
    propagateST solver

propagateST :: Solver -> IO Bool
propagateST solver = do
  tol <- getTolerance solver
  lim <- getIterationLimit solver
  ne <- getNEdges solver
  nv <- getNVars solver
  let loop !i
        | Just l <- lim, i > l = return False
        | otherwise = do
            numLoop 0 (ne-1) $ \e -> updateEdgeProb solver e
            let f maxDelta e = max maxDelta <$> updateEdgeSurvey solver e
            delta <- foldM f 0 [0 .. ne-1]
            if delta <= tol then do
              numLoop 1 nv $ \v -> computeVarProb solver v
              return True
            else
              loop (i+1)
  loop 0

data WorkerCommand
  = WCUpdateEdgeProb
  | WCUpdateSurvey
  | WCComputeVarProb
  | WCTerminate

propagateMT :: Solver -> Int -> IO Bool
propagateMT solver nthreads = do
  tol <- getTolerance solver
  lim <- getIterationLimit solver
  ne <- getNEdges solver
  nv <- getNVars solver

  mask $ \restore -> do
    ex <- newEmptyTMVarIO
    let wait :: STM a -> IO a
        wait m = join $ atomically $ liftM return m `orElse` liftM throwIO (takeTMVar ex)

    workers <- do
      let mE = (ne + nthreads - 1) `div` nthreads
          mV = (nv + nthreads - 1) `div` nthreads
      forM [0..nthreads-1] $ \i -> do
         let lbE = mE * i
             ubE = min (lbE + mE) ne
             lbV = mV * i + 1
             ubV = min (lbV + mV) nv + 1
         reqVar   <- newEmptyMVar
         respVar  <- newEmptyTMVarIO
         respVar2 <- newEmptyTMVarIO
         th <- forkIO $ do
           let loop = do
                 cmd <- takeMVar reqVar
                 case cmd of
                   WCTerminate -> return ()
                   WCUpdateEdgeProb -> do
                     numLoop lbE (ubE-1) $ \e -> updateEdgeProb solver e
                     atomically $ putTMVar respVar ()
                     loop
                   WCUpdateSurvey -> do
                     let f maxDelta e = max maxDelta <$> updateEdgeSurvey solver e
                     delta <- foldM f 0 [lbE .. ubE-1]
                     atomically $ putTMVar respVar2 delta
                     loop
                   WCComputeVarProb -> do
                     numLoop lbV (ubV-1) $ \v -> computeVarProb solver v
                     atomically $ putTMVar respVar ()
                     loop
           restore loop `catch` \(e :: SomeException) -> atomically (tryPutTMVar ex e >> return ())
         return (th, reqVar, respVar, respVar2)
 
    let loop !i
          | Just l <- lim, i > l = return False
          | otherwise = do
              mapM_ (\(_,reqVar,_,_) -> putMVar reqVar WCUpdateEdgeProb) workers
              mapM_ (\(_,_,respVar,_) -> wait (takeTMVar respVar)) workers
              mapM_ (\(_,reqVar,_,_) -> putMVar reqVar WCUpdateSurvey) workers
              delta <- foldM (\delta (_,_,_,respVar2) -> max delta <$> wait (takeTMVar respVar2)) 0 workers
              if delta <= tol then do
                mapM_ (\(_,reqVar,_,_) -> putMVar reqVar WCComputeVarProb) workers
                mapM_ (\(_,_,respVar,_) -> wait (takeTMVar respVar)) workers
                mapM_ (\(_,reqVar,_,_) -> putMVar reqVar WCTerminate) workers
                return True
              else
                loop (i+1)

    ret <- try $ restore $ loop 0
    case ret of
      Right b -> return b
      Left (e :: SomeException) -> do
        mapM_ (\(th,_,_,_) -> killThread th) workers
        throwIO e

updateEdgeProb :: Solver -> EdgeIndex -> IO ()
updateEdgeProb solver e = do
  let lit = svEdgeLit solver ! e
      j = abs lit
      a = svEdgeClause solver ! e
  m <- VGM.read (svVarFixed solver) (j - 1)
  case m of
    Just b -> do
      let flag = (lit > 0) == b
      VGM.write (svEdgeProbU solver) e (if flag then 0 else 1) -- Π^u_{j→a}
      VGM.write (svEdgeProbS solver) e (if flag then 1 else 0) -- Π^s_{j→a}
      VGM.write (svEdgeProb0 solver) e 0                       -- Π^0_{j→a}
    Nothing -> do
      let f :: (Double, Double) -> EdgeIndex -> IO (Double, Double)
          f (!val1, !val2) e2 = do
            let b = svEdgeClause solver ! e2
                lit2 = svEdgeLit solver ! e2
            if a==b then
              return (val1, val2)
            else do
              eta_bj <- VGM.read (svEdgeSurvey solver) e2 -- η_{b→j}
              let w = svClauseWeight solver ! b
              let val1' = if signum lit == signum lit2 then val1 * (1 - eta_bj) ** w else val1
                  val2' = if signum lit /= signum lit2 then val2 * (1 - eta_bj) ** w else val2
              return (val1',val2')
      (val1,val2) <- foldM f (1,1) (svVarEdges solver ! (j - 1))
      -- val1 = Π_{V^s_a(j) \ a} (1 - η_{b→j})
      -- val2 = Π_{V^u_a(j) \ a} (1 - η_{b→j})
      VGM.write (svEdgeProbU solver) e ((1 - val2) * val1) -- Π^u_{j→a}
      VGM.write (svEdgeProbS solver) e ((1 - val1) * val2) -- Π^s_{j→a}
      VGM.write (svEdgeProb0 solver) e (val1 * val2)       -- Π^0_{j→a}

updateEdgeSurvey :: Solver -> EdgeIndex -> IO Double
updateEdgeSurvey solver e = do
  let a = svEdgeClause solver ! e
      lit = svEdgeLit solver ! e
      i = abs lit
      f :: Double -> EdgeIndex -> IO Double
      f !p e2 = do
        let lit2 = svEdgeLit solver ! e2
            j = abs lit2
        if i == j then
          return p
        else do
          pu <- VGM.read (svEdgeProbU solver) e2 -- Π^u_{j→a}
          ps <- VGM.read (svEdgeProbS solver) e2 -- Π^s_{j→a}
          p0 <- VGM.read (svEdgeProb0 solver) e2 -- Π^0_{j→a}
          -- (pu / (pu + ps + p0)) is the probability of lit being false, if the edge does not exist.
          return $! p * (pu / (pu + ps + p0))
  eta_ai <- VGM.read (svEdgeSurvey solver) e
  eta_ai' <- foldM f 1 (svClauseEdges solver ! a)
  VGM.write (svEdgeSurvey solver) e eta_ai'
  return $! abs (eta_ai' - eta_ai)

computeVarProb :: Solver -> SAT.Var -> IO ()
computeVarProb solver v = do
  let i = v - 1
      f (val1,val2) e = do
        let lit = svEdgeLit solver ! e
            a = svEdgeClause solver ! e
            w = svClauseWeight solver ! a
        eta_ai <- VGM.read (svEdgeSurvey solver) e
        let val1' = if lit > 0 then val1 * (1 - eta_ai) ** w else val1
            val2' = if lit < 0 then val2 * (1 - eta_ai) ** w else val2
        return (val1',val2')
  (val1,val2) <- foldM f (1,1) (svVarEdges solver ! i)
  let p0 = val1 * val2       -- \^{Π}^{0}_i
      pp = (1 - val1) * val2 -- \^{Π}^{+}_i
      pn = (1 - val2) * val1 -- \^{Π}^{-}_i
  let wp = pp / (pp + pn + p0)
      wn = pn / (pp + pn + p0)
  VGM.write (svVarProbT solver) i wp -- W^{(+)}_i
  VGM.write (svVarProbF solver) i wn -- W^{(-)}_i

-- | Get the marginal probability of the variable to be @True@, @False@ and unspecified respectively.
getVarProb :: Solver -> SAT.Var -> IO (Double, Double, Double)
getVarProb solver v = do
  pt <- VGM.read (svVarProbT solver) (v - 1)
  pf <- VGM.read (svVarProbF solver) (v - 1)
  return (pt, pf, 1 - (pt + pf))

findLargestBiasLit :: Solver -> IO (Maybe SAT.Lit)
findLargestBiasLit solver = do
  nv <- getNVars solver
  let f (!lit,!maxBias) v = do
        let i = v - 1
        m <- VGM.read (svVarFixed solver) i
        case m of
          Just _ -> return (lit,maxBias)
          Nothing -> do
            (pt,pf,_) <- getVarProb solver v
            let bias = pt - pf
            if lit == 0 || abs bias > maxBias then do
              if bias >= 0 then
                return (v, bias)
              else
                return (-v, abs bias)
            else
              return (lit, maxBias)
  (lit,_) <- foldM f (0,0) [1..nv]
  if lit == 0 then
    return Nothing
  else
    return (Just lit)

fixLit :: Solver -> SAT.Lit -> IO ()
fixLit solver lit = do
  VGM.write (svVarFixed solver) (abs lit - 1) (if lit > 0 then Just True else Just False)

unfixLit :: Solver -> SAT.Lit -> IO ()
unfixLit solver lit = do
  VGM.write (svVarFixed solver) (abs lit - 1) Nothing

checkConsis :: Solver -> IO Bool
checkConsis solver = do
  nc <- getNConstraints solver
  let loop i | i >= nc = return True
      loop i = do
        let loop2 [] = return False
            loop2 (e : es) = do
              let lit = svEdgeLit solver ! e
              m <- VM.read (svVarFixed solver) (abs lit - 1)
              case m of
                Nothing -> return True
                Just b -> if b == (lit > 0) then return True else loop2 es
        b <- loop2 (svClauseEdges solver ! i)
        if b then
          loop (i + 1)
        else
          return False
  loop 0

solve :: Solver -> IO (Maybe SAT.Model)
solve solver = do
  nv <- getNVars solver
  let loop :: IO (Maybe SAT.Model)
      loop = do
        b <- checkConsis solver
        if not b then
          return Nothing
        else do
          b2 <- propagate solver
          if not b2 then
            return Nothing
          else do
            mlit <- findLargestBiasLit solver
            case mlit of
              Just lit -> do
                putStrLn $ "fixing literal " ++ show lit
                fixLit solver lit
                ret <- loop
                case ret of
                  Just m -> return (Just m)
                  Nothing -> do
                    putStrLn $ "literal " ++ show lit ++ " failed; flipping to " ++ show (-lit)
                    fixLit solver (-lit)
                    ret2 <- loop
                    case ret2 of
                      Just m -> return (Just m)
                      Nothing -> do
                        putStrLn $ "both literal " ++ show lit ++ " and " ++ show (-lit) ++ " failed; backtracking"
                        unfixLit solver lit
                        return Nothing
              Nothing -> do
                xs <- forM [1..nv] $ \v -> do
                  m2 <- VGM.read (svVarFixed solver) (v-1)
                  return (v, fromJust m2)
                return $ Just $ A.array (1,nv) xs
  loop

printInfo :: Solver -> IO ()
printInfo solver = do
  (surveys :: VU.Vector Double) <- VG.freeze (svEdgeSurvey solver)
  (s :: VU.Vector Double) <- VG.freeze (svEdgeProbS solver)
  (u :: VU.Vector Double) <- VG.freeze (svEdgeProbU solver)
  (z :: VU.Vector Double) <- VG.freeze (svEdgeProb0 solver)
  let xs = [(clause, lit, eta, s ! e, u ! e, z ! e) | (e, eta) <- zip [0..] (VG.toList surveys), let lit = svEdgeLit solver ! e, let clause = svEdgeClause solver ! e]
  putStrLn $ "edges: " ++ show xs

  (pt :: VU.Vector Double) <- VG.freeze (svVarProbT solver)
  (pf :: VU.Vector Double) <- VG.freeze (svVarProbF solver)
  nv <- getNVars solver
  let xs2 = [(v, pt ! i, pf ! i, (pt ! i) - (pf ! i)) | v <- [1..nv], let i = v - 1]
  putStrLn $ "vars: " ++ show xs2
