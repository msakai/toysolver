{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
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
--
-- * Corrie Scalisi. Visualizing Survey Propagation in 3-SAT Factor Graphs,
--   <http://classes.soe.ucsc.edu/cmps290c/Winter06/proj/corriereport.pdf>.
--
-----------------------------------------------------------------------------
module ToySolver.SAT.MessagePassing.SurveyPropagation
  (
  -- * The Solver type
    Solver
  , newSolver
  , deleteSolver

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
  , initializeRandomDirichlet
  , propagate
  , getVarProb

  -- * Solving
  , fixLit
  , unfixLit

  -- * Debugging
  , printInfo
  ) where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Exception
import Control.Loop
import Control.Monad
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.IORef
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as VM
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import Data.Vector.Generic ((!))
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Generic.Mutable as VGM
import qualified Numeric.Log as L
import qualified System.Random.MWC as Rand
import qualified System.Random.MWC.Distributions as Rand

import qualified ToySolver.SAT.Types as SAT

infixr 8 ^*

(^*) :: Num a => L.Log a -> a -> L.Log a
L.Exp a ^* b = L.Exp (a*b)

comp :: (RealFloat a, L.Precise a) => L.Log a -> L.Log a
comp (L.Exp a) = L.Exp $ L.log1p $ max (-1) $ negate (exp a)

type ClauseIndex = Int
type EdgeIndex   = Int

data Solver
  = Solver
  { svVarEdges :: !(V.Vector (VU.Vector EdgeIndex))
  , svVarProbT :: !(VUM.IOVector (L.Log Double))
  , svVarProbF :: !(VUM.IOVector (L.Log Double))
  , svVarFixed :: !(VM.IOVector (Maybe Bool))

  , svClauseEdges :: !(V.Vector (VU.Vector EdgeIndex))
  , svClauseWeight :: !(VU.Vector Double)

  , svEdgeLit    :: !(VU.Vector SAT.Lit) -- i
  , svEdgeClause :: !(VU.Vector ClauseIndex) -- a
  , svEdgeSurvey :: !(VUM.IOVector (L.Log Double)) -- η_{a → i}
  , svEdgeProbU  :: !(VUM.IOVector (L.Log Double)) -- Π^u_{i → a} / (Π^u_{i → a} + Π^s_{i → a} + Π^0_{i → a})

  , svTolRef :: !(IORef Double)
  , svIterLimRef :: !(IORef (Maybe Int))
  , svNThreadsRef :: !(IORef Int)
  }

newSolver :: Int -> [(Double, SAT.PackedClause)] -> IO Solver
newSolver nv clauses = do
  let num_clauses = length clauses
      num_edges = sum [VG.length c | (_,c) <- clauses]

  varEdgesRef <- newIORef IntMap.empty
  clauseEdgesM <- VGM.new num_clauses

  (edgeLitM :: VUM.IOVector SAT.Lit) <- VGM.new num_edges
  (edgeClauseM :: VUM.IOVector ClauseIndex) <- VGM.new num_edges

  ref <- newIORef 0
  forM_ (zip [0..] clauses) $ \(i,(_,c)) -> do
    es <- forM (SAT.unpackClause c) $ \lit -> do
      e <- readIORef ref
      modifyIORef' ref (+1)
      modifyIORef' varEdgesRef (IntMap.insertWith IntSet.union (abs lit) (IntSet.singleton e))
      VGM.unsafeWrite edgeLitM e lit
      VGM.unsafeWrite edgeClauseM e i
      return e
    VGM.unsafeWrite clauseEdgesM i (VG.fromList es)

  varEdges <- readIORef varEdgesRef
  clauseEdges <- VG.unsafeFreeze clauseEdgesM

  edgeLit     <- VG.unsafeFreeze edgeLitM
  edgeClause  <- VG.unsafeFreeze edgeClauseM

  -- Initialize all surveys with non-zero values.
  -- If we initialize to zero, following trivial solution exists:
  -- 
  -- η_{a→i} = 0 for all i and a.
  -- 
  -- Π^0_{i→a} = 1, Π^u_{i→a} = Π^s_{i→a} = 0 for all i and a,
  -- 
  -- \^{Π}^{0}_i = 1, \^{Π}^{+}_i = \^{Π}^{-}_i = 0
  -- 
  edgeSurvey  <- VGM.replicate num_edges 0.5
  edgeProbU   <- VGM.new num_edges

  varFixed <- VGM.replicate nv Nothing
  varProbT <- VGM.new nv
  varProbF <- VGM.new nv

  tolRef <- newIORef 0.01
  maxIterRef <- newIORef (Just 1000)
  nthreadsRef <- newIORef 1

  let solver = Solver
        { svVarEdges    = VG.generate nv $ \i ->
            case IntMap.lookup (i+1) varEdges of
              Nothing -> VG.empty
              Just es -> VG.fromListN (IntSet.size es) (IntSet.toList es)
        , svVarProbT = varProbT
        , svVarProbF = varProbF
        , svVarFixed = varFixed

        , svClauseEdges = clauseEdges
        , svClauseWeight = VG.fromListN (VG.length clauseEdges) (map fst clauses)

        , svEdgeLit     = edgeLit
        , svEdgeClause  = edgeClause
        , svEdgeSurvey  = edgeSurvey
        , svEdgeProbU   = edgeProbU

        , svTolRef = tolRef
        , svIterLimRef = maxIterRef
        , svNThreadsRef = nthreadsRef
        }

  return solver

deleteSolver :: Solver -> IO ()
deleteSolver _solver = return ()

initializeRandom :: Solver -> Rand.GenIO -> IO ()
initializeRandom solver gen = do
  VG.forM_ (svClauseEdges solver) $ \es -> do
    case VG.length es of
      0 -> return ()
      1 -> VGM.unsafeWrite (svEdgeSurvey solver) (es ! 0) 1
      n -> do
        let p :: Double
            p = 1 / fromIntegral n
        VG.forM_ es $ \e -> do
          d <- Rand.uniformR (p*0.5, p*1.5) gen
          VGM.unsafeWrite (svEdgeSurvey solver) e (realToFrac d)

initializeRandomDirichlet :: Solver -> Rand.GenIO -> IO ()
initializeRandomDirichlet solver gen = do
  VG.forM_ (svClauseEdges solver) $ \es -> do
    case VG.length es of
      0 -> return ()
      1 -> VGM.unsafeWrite (svEdgeSurvey solver) (es ! 0) 1
      len -> do
        (ps :: V.Vector Double) <- Rand.dirichlet (VG.replicate len 1) gen
        numLoop 0 (len-1) $ \i -> do
          VGM.unsafeWrite (svEdgeSurvey solver) (es ! i) (realToFrac (ps ! i))

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
  nv <- getNVars solver
  nc <- getNConstraints solver
  let max_v_len = VG.maximum $ VG.map VG.length $ svVarEdges solver
      max_c_len = VG.maximum $ VG.map VG.length $ svClauseEdges solver
  tmp <- VGM.new (max (max_v_len * 2) max_c_len)
  let loop !i
        | Just l <- lim, i >= l = return False
        | otherwise = do
            numLoop 1 nv $ \v -> updateEdgeProb solver v tmp
            let f maxDelta c = max maxDelta <$> updateEdgeSurvey solver c tmp
            delta <- foldM f 0 [0 .. nc-1]
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
  nv <- getNVars solver
  nc <- getNConstraints solver

  mask $ \restore -> do
    ex <- newEmptyTMVarIO
    let wait :: STM a -> IO a
        wait m = join $ atomically $ liftM return m `orElse` liftM throwIO (takeTMVar ex)

    workers <- do
      let mV = (nv + nthreads - 1) `div` nthreads
          mC = (nc + nthreads - 1) `div` nthreads
      forM [0..nthreads-1] $ \i -> do
         let lbV = mV * i + 1 -- inclusive
             ubV = min (lbV + mV) (nv + 1) -- exclusive
             lbC = mC * i -- exclusive
             ubC = min (lbC + mC) nc -- exclusive
         let max_v_len = VG.maximum $ VG.map VG.length $ VG.slice (lbV - 1) (ubV - lbV) (svVarEdges solver)
             max_c_len = VG.maximum $ VG.map VG.length $ VG.slice lbC (ubC - lbC) (svClauseEdges solver)
         tmp <- VGM.new (max (max_v_len*2) max_c_len)
         reqVar   <- newEmptyMVar
         respVar  <- newEmptyTMVarIO
         respVar2 <- newEmptyTMVarIO
         th <- forkIO $ do
           let loop = do
                 cmd <- takeMVar reqVar
                 case cmd of
                   WCTerminate -> return ()
                   WCUpdateEdgeProb -> do
                     numLoop lbV (ubV-1) $ \v -> updateEdgeProb solver v tmp
                     atomically $ putTMVar respVar ()
                     loop
                   WCUpdateSurvey -> do
                     let f maxDelta c = max maxDelta <$> updateEdgeSurvey solver c tmp
                     delta <- foldM f 0 [lbC .. ubC-1]
                     atomically $ putTMVar respVar2 delta
                     loop
                   WCComputeVarProb -> do
                     numLoop lbV (ubV-1) $ \v -> computeVarProb solver v
                     atomically $ putTMVar respVar ()
                     loop
           restore loop `catch` \(e :: SomeException) -> atomically (tryPutTMVar ex e >> return ())
         return (th, reqVar, respVar, respVar2)
 
    let loop !i
          | Just l <- lim, i >= l = return False
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

-- tmp1 must have at least @VG.length (svVarEdges solver ! (v - 1)) * 2@ elements
updateEdgeProb :: Solver -> SAT.Var -> VUM.IOVector (L.Log Double) -> IO ()
updateEdgeProb solver v tmp = do
  let i = v - 1
      edges = svVarEdges solver ! i
  m <- VGM.unsafeRead (svVarFixed solver) i
  case m of
    Just val -> do
      VG.forM_ edges $ \e -> do
        let lit = svEdgeLit solver ! e
            flag = (lit > 0) == val
        VGM.unsafeWrite (svEdgeProbU solver) e (if flag then 0 else 1)
    Nothing -> do
      let f !k !val1_pre !val2_pre
            | k >= VG.length edges = return ()
            | otherwise = do
                let e = edges ! k
                    a = svEdgeClause solver ! e
                VGM.unsafeWrite tmp (k*2) val1_pre
                VGM.unsafeWrite tmp (k*2+1) val2_pre
                eta_ai <- VGM.unsafeRead (svEdgeSurvey solver) e -- η_{a→i}
                let w = svClauseWeight solver ! a
                    lit2 = svEdgeLit solver ! e
                    val1_pre' = if lit2 > 0 then val1_pre * comp eta_ai ^* w else val1_pre
                    val2_pre' = if lit2 > 0 then val2_pre else val2_pre * comp eta_ai ^* w
                f (k+1) val1_pre' val2_pre'
      f 0 1 1
      -- tmp ! (k*2)   == Π_{a∈edges[0..k-1], a∈V^{+}(i)} (1 - eta_ai)^{w_i}
      -- tmp ! (k*2+1) == Π_{a∈edges[0..k-1], a∈V^{-}(i)} (1 - eta_ai)^{w_i}

      let g !k !val1_post !val2_post
            | k < 0 = return ()
            | otherwise = do
                let e = edges ! k
                    a = svEdgeClause solver ! e
                    lit2 = svEdgeLit solver ! e
                val1_pre <- VGM.unsafeRead tmp (k*2)
                val2_pre <- VGM.unsafeRead tmp (k*2+1)
                let val1 = val1_pre * val1_post -- val1 == Π_{b∈edges, b∈V^{+}(i), a≠b} (1 - eta_bi)^{w_i}
                    val2 = val2_pre * val2_post -- val2 == Π_{b∈edges, b∈V^{-}(i), a≠b} (1 - eta_bi)^{w_i}
                eta_ai <- VGM.unsafeRead (svEdgeSurvey solver) e -- η_{a→i}
                let w = svClauseWeight solver ! a
                    val1_post' = if lit2 > 0 then val1_post * comp eta_ai ^* w else val1_post
                    val2_post' = if lit2 > 0 then val2_post else val2_post * comp eta_ai ^* w
                let pi_0 = val1 * val2 -- Π^0_{i→a}
                    pi_u = if lit2 > 0 then comp val2 * val1 else comp val1 * val2 -- Π^u_{i→a}
                    pi_s = if lit2 > 0 then comp val1 * val2 else comp val2 * val1 -- Π^s_{i→a}
                VGM.unsafeWrite (svEdgeProbU solver) e (pi_u / L.sum [pi_0, pi_u, pi_s])
                g (k-1) val1_post' val2_post'
      g (VG.length edges - 1) 1 1

-- tmp must have at least @VG.length (svClauseEdges solver ! a)@ elements
updateEdgeSurvey :: Solver -> ClauseIndex -> VUM.IOVector (L.Log Double) -> IO Double
updateEdgeSurvey solver a tmp = do
  let edges = svClauseEdges solver ! a
  let f !k !p_pre
        | k >= VG.length edges = return ()
        | otherwise = do
            let e = edges ! k
            VGM.unsafeWrite tmp k p_pre
            p <- VGM.unsafeRead (svEdgeProbU solver) e
            -- p is the probability of lit being false, if the edge does not exist.
            f (k+1) (p_pre * p)
  let g !k !p_post !maxDelta
        | k < 0 = return maxDelta
        | otherwise = do
            let e = edges ! k
            -- p_post == Π_{e∈edges[k+1..]} p_e
            p_pre <- VGM.unsafeRead tmp k -- Π_{e∈edges[0..k-1]} p_e
            p <- VGM.unsafeRead (svEdgeProbU solver) e
            eta_ai <- VGM.unsafeRead (svEdgeSurvey solver) e
            let eta_ai' = p_pre * p_post -- Π_{e∈edges[0,..,k-1,k+1,..]} p_e
            VGM.unsafeWrite (svEdgeSurvey solver) e eta_ai'
            let delta = abs (realToFrac eta_ai' - realToFrac eta_ai)
            g (k-1) (p_post * p) (max delta maxDelta)
  f 0 1
  -- tmp ! k == Π_{e∈edges[0..k-1]} p_e
  g (VG.length edges - 1) 1 0

computeVarProb :: Solver -> SAT.Var -> IO ()
computeVarProb solver v = do
  let i = v - 1
      f (val1,val2) e = do
        let lit = svEdgeLit solver ! e
            a = svEdgeClause solver ! e
            w = svClauseWeight solver ! a
        eta_ai <- VGM.unsafeRead (svEdgeSurvey solver) e
        let val1' = if lit > 0 then val1 * comp eta_ai ^* w else val1
            val2' = if lit < 0 then val2 * comp eta_ai ^* w else val2
        return (val1',val2')
  (val1,val2) <- VG.foldM' f (1,1) (svVarEdges solver ! i)
  let p0 = val1 * val2       -- \^{Π}^{0}_i
      pp = comp val1 * val2 -- \^{Π}^{+}_i
      pn = comp val2 * val1 -- \^{Π}^{-}_i
  let wp = pp / (pp + pn + p0)
      wn = pn / (pp + pn + p0)
  VGM.unsafeWrite (svVarProbT solver) i wp -- W^{(+)}_i
  VGM.unsafeWrite (svVarProbF solver) i wn -- W^{(-)}_i

-- | Get the marginal probability of the variable to be @True@, @False@ and unspecified respectively.
getVarProb :: Solver -> SAT.Var -> IO (Double, Double, Double)
getVarProb solver v = do
  pt <- realToFrac <$> VGM.unsafeRead (svVarProbT solver) (v - 1)
  pf <- realToFrac <$> VGM.unsafeRead (svVarProbF solver) (v - 1)
  return (pt, pf, 1 - (pt + pf))

fixLit :: Solver -> SAT.Lit -> IO ()
fixLit solver lit = do
  VGM.unsafeWrite (svVarFixed solver) (abs lit - 1) (if lit > 0 then Just True else Just False)

unfixLit :: Solver -> SAT.Lit -> IO ()
unfixLit solver lit = do
  VGM.unsafeWrite (svVarFixed solver) (abs lit - 1) Nothing

printInfo :: Solver -> IO ()
printInfo solver = do
  (surveys :: VU.Vector (L.Log Double)) <- VG.freeze (svEdgeSurvey solver)
  (u :: VU.Vector (L.Log Double)) <- VG.freeze (svEdgeProbU solver)
  let xs = [(clause, lit, eta, u ! e) | (e, eta) <- zip [0..] (VG.toList surveys), let lit = svEdgeLit solver ! e, let clause = svEdgeClause solver ! e]
  putStrLn $ "edges: " ++ show xs

  (pt :: VU.Vector (L.Log Double)) <- VG.freeze (svVarProbT solver)
  (pf :: VU.Vector (L.Log Double)) <- VG.freeze (svVarProbF solver)
  nv <- getNVars solver
  let xs2 = [(v, realToFrac (pt ! i) :: Double, realToFrac (pf ! i) :: Double, realToFrac (pt ! i) - realToFrac (pf ! i) :: Double) | v <- [1..nv], let i = v - 1]
  putStrLn $ "vars: " ++ show xs2
