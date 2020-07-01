{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Arith.MIP
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Naïve implementation of MIP solver based on Simplex module
--
-- Reference:
--
-- * <http://www.math.cuhk.edu.hk/~wei/lpch3.pdf>
--
-- * Ralph E. Gomory.
--   \"An Algorithm for the Mixed Integer Problem\", Technical Report
--   RM-2597, 1960, The Rand Corporation, Santa Monica, CA.
--   <http://www.rand.org/pubs/research_memoranda/RM2597.html>
--
-- * Ralph E. Gomory.
--   \"Outline of an algorithm for integer solutions to linear programs\".
--   Bull. Amer. Math. Soc., Vol. 64, No. 5. (1958), pp. 275-278.
--   <http://projecteuclid.org/euclid.bams/1183522679>
--
-- * R. C. Daniel and Martyn Jeffreys.
--   \"Unboundedness in Integer and Discrete Programming L.P. Relaxations\"
--   The Journal of the Operational Research Society, Vol. 30, No. 12. (1979)
--   <http://www.jstor.org/stable/3009435>
--
-----------------------------------------------------------------------------
module ToySolver.Arith.MIP
  (
  -- * The @Solver@ type
    Solver
  , newSolver

  -- * Solving
  , optimize

  -- * Extract results
  , getBestSolution
  , getBestValue
  , getBestModel

  -- * Configulation
  , setNThread
  , setLogger
  , setOnUpdateBestSolution
  , setShowRational
  ) where

import Prelude hiding (log)

import Control.Monad
import Control.Exception
import Control.Concurrent
import Control.Concurrent.STM
import Data.Default.Class
import Data.List
import Data.OptDir
import Data.Ord
import Data.IORef
import Data.Maybe
import qualified Data.IntSet as IS
import qualified Data.IntMap as IM
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Foldable as F
import Data.VectorSpace
import System.Clock
import System.Timeout
import Text.Printf

import qualified ToySolver.Data.LA as LA
import ToySolver.Data.OrdRel ((.<=.), (.>=.))
import qualified ToySolver.Arith.Simplex as Simplex
import ToySolver.Arith.Simplex (OptResult (..), Var, Model)
import ToySolver.Internal.Util (isInteger, fracPart)

data Solver
  = MIP
  { mipRootLP :: Simplex.Solver
  , mipIVs    :: IS.IntSet
  , mipBest   :: TVar (Maybe Node)

  , mipNThread :: IORef Int
  , mipLogger  :: IORef (Maybe (String -> IO ()))
  , mipOnUpdateBestSolution :: IORef (Model -> Rational -> IO ())
  , mipShowRational :: IORef Bool
  }

data Node =
  Node
  { ndLP    :: Simplex.Solver
  , ndDepth :: {-# UNPACK #-} !Int
  , ndValue :: Rational
  }

newSolver :: Simplex.Solver -> IS.IntSet -> IO Solver
newSolver lp ivs = do
  lp2 <- Simplex.cloneSolver lp

  forM_ (IS.toList ivs) $ \v -> do
    lb <- Simplex.getLB lp2 v
    case lb of
      Just (l,_) | not (isInteger l) ->
        Simplex.assertLower lp2 v (fromInteger (ceiling l))
      _ -> return ()
    ub <- Simplex.getUB lp2 v
    case ub of
      Just (u,_) | not (isInteger u) ->
        Simplex.assertLower lp2 v (fromInteger (floor u))
      _ -> return ()

  bestRef <- newTVarIO Nothing

  nthreadRef <- newIORef 0
  logRef  <- newIORef Nothing
  showRef <- newIORef False
  updateRef <- newIORef (\_ _ -> return ())

  return $
    MIP
    { mipRootLP = lp2
    , mipIVs    = ivs
    , mipBest   = bestRef

    , mipNThread = nthreadRef
    , mipLogger = logRef
    , mipOnUpdateBestSolution = updateRef
    , mipShowRational = showRef
    }

optimize :: Solver -> IO OptResult
optimize solver = do
  let lp = mipRootLP solver
  update <- readIORef (mipOnUpdateBestSolution solver)
  log solver "MIP: Solving LP relaxation..."
  ret <- Simplex.check lp
  if not ret
  then return Unsat
  else do
    s0 <- showValue solver =<< Simplex.getObjValue lp
    log solver (printf "MIP: LP relaxation is satisfiable with obj = %s" s0)
    log solver "MIP: Optimizing LP relaxation"
    ret2 <- Simplex.optimize lp def
    case ret2 of
      Unsat    -> error "should not happen"
      ObjLimit -> error "should not happen"
      Unbounded -> do
        log solver "MIP: LP relaxation is unbounded"
        let ivs = mipIVs solver
        if IS.null ivs
          then return Unbounded
          else do
            {-
              * In general, original problem may have optimal
                solution even though LP relaxiation is unbounded.
              * But if restricted to rational numbers, the
                original problem is unbounded or unsatisfiable
                when LP relaxation is unbounded.
            -}
            origObj <- Simplex.getObj lp
            lp2 <- Simplex.cloneSolver lp
            Simplex.clearLogger lp2
            Simplex.setObj lp2 (LA.constant 0)
            branchAndBound solver lp2 $ \m _ -> do
              update m (LA.eval m origObj)
            best <- readTVarIO (mipBest solver)
            case best of
              Just nd -> do
                m <- Simplex.getModel (ndLP nd)
                atomically $ writeTVar (mipBest solver) $ Just nd{ ndValue = LA.eval m origObj }
                return Unbounded
              Nothing -> return Unsat
      Optimum -> do
        s1 <- showValue solver =<< Simplex.getObjValue lp
        log solver $ "MIP: LP relaxation optimum is " ++ s1
        log solver "MIP: Integer optimization begins..."
        Simplex.clearLogger lp
        branchAndBound solver lp update
        m <- readTVarIO (mipBest solver)
        case m of
          Nothing -> return Unsat
          Just _ -> return Optimum

branchAndBound :: Solver -> Simplex.Solver -> (Model -> Rational -> IO ()) -> IO ()
branchAndBound solver rootLP update = do
  dir <- Simplex.getOptDir rootLP
  rootVal <- Simplex.getObjValue rootLP
  let root = Node{ ndLP = rootLP, ndDepth = 0, ndValue = rootVal }

  pool <- newTVarIO (Seq.singleton root)
  activeThreads <- newTVarIO (Map.empty)
  visitedNodes <- newTVarIO 0
  solchan <- newTChanIO

  let addNode :: Node -> STM ()
      addNode nd = do
        modifyTVar pool (Seq.|> nd)

      pickNode :: IO (Maybe Node)
      pickNode = do
        self <- myThreadId
        atomically $ modifyTVar activeThreads (Map.delete self)
        atomically $ do
          s <- readTVar pool
          case Seq.viewl s of
            nd Seq.:< s2 -> do
              writeTVar pool s2
              modifyTVar activeThreads (Map.insert self nd)
              return (Just nd)
            Seq.EmptyL -> do
              ths <- readTVar activeThreads
              if Map.null ths
                then return Nothing
                else retry

      processNode :: Node -> IO ()
      processNode node = do
        let lp = ndLP node
        lim <- liftM (fmap ndValue) $ readTVarIO (mipBest solver)
        ret <- Simplex.dualSimplex lp def{ Simplex.objLimit = lim }

        case ret of
          Unbounded -> error "should not happen"
          Unsat ->  return ()
          ObjLimit -> return ()
          Optimum -> do
            val <- Simplex.getObjValue lp
            p <- prune solver val
            unless p $ do
              xs <- violated node (mipIVs solver)
              case xs of
                [] -> atomically $ writeTChan solchan $ node { ndValue = val }
                _ -> do
                  r <- if ndDepth node `mod` 100 /= 0
                       then return Nothing
                       else liftM listToMaybe $ filterM (canDeriveGomoryCut lp) $ map fst xs
                  case r of
                    Nothing -> do -- branch
                      let (v0,val0) = fst $ maximumBy (comparing snd)
                                      [((v,vval), abs (fromInteger (round vval) - vval)) | (v,vval) <- xs]
                      let lp1 = lp
                      lp2 <- Simplex.cloneSolver lp
                      Simplex.assertAtom lp1 (LA.var v0 .<=. LA.constant (fromInteger (floor val0)))
                      Simplex.assertAtom lp2 (LA.var v0 .>=. LA.constant (fromInteger (ceiling val0)))
                      atomically $ do
                        addNode $ Node lp1 (ndDepth node + 1) val
                        addNode $ Node lp2 (ndDepth node + 1) val
                        modifyTVar visitedNodes (+1)
                    Just v -> do -- cut
                      atom <- deriveGomoryCut lp (mipIVs solver) v
                      Simplex.assertAtom lp atom
                      atomically $ do
                        addNode $ Node lp (ndDepth node + 1) val

  let isCompleted = do
        nodes <- readTVar pool
        threads <- readTVar activeThreads
        return $ Seq.null nodes && Map.null threads

  -- fork worker threads
  nthreads <- liftM (max 1) $ readIORef (mipNThread solver)

  log solver $ printf "MIP: forking %d worker threads..." nthreads

  startCPU <- getTime ProcessCPUTime
  startWC  <- getTime Monotonic
  ex <- newEmptyTMVarIO

  let printStatus :: Seq.Seq Node -> Int -> IO ()
      printStatus nodes visited
        | Seq.null nodes = return () -- should not happen
        | otherwise = do
            nowCPU <- getTime ProcessCPUTime
            nowWC  <- getTime Monotonic
            let spentCPU = sec (nowCPU `diffTimeSpec` startCPU)
            let spentWC  = sec (nowWC  `diffTimeSpec` startWC )

            let vs = map ndValue (F.toList nodes)
                dualBound =
                  case dir of
                    OptMin -> minimum vs
                    OptMax -> maximum vs

            primalBound <- do
              x <- readTVarIO (mipBest solver) -- TODO: 引数にするようにした方が良い?
              return $ case x of
                Nothing -> Nothing
                Just node -> Just (ndValue node)

            (p,g) <- case primalBound of
                   Nothing -> return ("not yet found", "--")
                   Just val -> do
                     p <- showValue solver val
                     let g = if val == 0
                             then "inf"
                             else printf "%.2f%%" (fromRational (abs (dualBound - val) * 100 / abs val) :: Double)
                     return (p, g)
            d <- showValue solver dualBound

            let range =
                  case dir of
                    OptMin -> p ++ " >= " ++ d
                    OptMax -> p ++ " <= " ++ d

            log solver $ printf "cpu time = %d sec; wc time = %d sec; active nodes = %d; visited nodes = %d; %s; gap = %s"
              spentCPU spentWC (Seq.length nodes) visited range g

  mask $ \(restore :: forall a. IO a -> IO a) -> do
    threads <- replicateM nthreads $ do
      forkIO $ do
        let loop = do
              m <- pickNode
              case m of
                Nothing -> return ()
                Just node -> processNode node >> loop
        ret <- try $ restore loop
        case ret of
          Left e -> atomically (putTMVar ex e)
          Right _ -> return ()

    let propagateException :: SomeException -> IO ()
        propagateException e = do
          mapM_ (\t -> throwTo t e) threads
          throwIO e

    let loop = do
          ret <- try $ timeout (2*1000*1000) $ restore $ atomically $ msum
            [ do node <- readTChan solchan
                 ret <- do
                   old <- readTVar (mipBest solver)
                   case old of
                     Nothing -> do
                       writeTVar (mipBest solver) (Just node)
                       return True
                     Just best -> do
                       let isBetter = if dir==OptMin then ndValue node < ndValue best else ndValue node > ndValue best
                       when isBetter $ writeTVar (mipBest solver) (Just node)
                       return isBetter
                 return $ do
                   when ret $ do
                     let lp = ndLP node
                     m <- Simplex.getModel lp
                     update m (ndValue node)
                   loop
            , do b <- isCompleted
                 guard b
                 return $ return ()
            , do e <- readTMVar ex
                 return $ propagateException e
            ]

          case ret of
            Left (e::SomeException) -> propagateException e
            Right (Just m) -> m
            Right Nothing -> do -- timeout
              (nodes, visited) <- atomically $ do
                nodes    <- readTVar pool
                athreads <- readTVar activeThreads
                visited  <- readTVar visitedNodes
                return (Seq.fromList (Map.elems athreads) Seq.>< nodes, visited)
              printStatus nodes visited
              loop

    loop

getBestSolution :: Solver -> IO (Maybe (Model, Rational))
getBestSolution solver = do
  ret <- readTVarIO (mipBest solver)
  case ret of
    Nothing -> return Nothing
    Just node -> do
      m <- Simplex.getModel (ndLP node)
      return $ Just (m, ndValue node)

getBestModel :: Solver -> IO (Maybe Model)
getBestModel solver = liftM (fmap fst) $ getBestSolution solver

getBestValue :: Solver -> IO (Maybe Rational)
getBestValue solver = liftM (fmap snd) $ getBestSolution solver

violated :: Node -> IS.IntSet -> IO [(Var, Rational)]
violated node ivs = do
  m <- Simplex.getModel (ndLP node)
  let p (v,val) = v `IS.member` ivs && not (isInteger val)
  return $ filter p (IM.toList m)

prune :: Solver -> Rational -> IO Bool
prune solver lb = do
  b <- readTVarIO (mipBest solver)
  case b of
    Nothing -> return False
    Just node -> do
      dir <- Simplex.getOptDir (mipRootLP solver)
      return $ if dir==OptMin then ndValue node <= lb else ndValue node >= lb

showValue :: Solver -> Rational -> IO String
showValue solver v = do
  printRat <- readIORef (mipShowRational solver)
  return $ Simplex.showValue printRat v

setShowRational :: Solver -> Bool -> IO ()
setShowRational solver = writeIORef (mipShowRational solver)

setNThread :: Solver -> Int -> IO ()
setNThread solver = writeIORef (mipNThread solver)

{--------------------------------------------------------------------
  Logging
--------------------------------------------------------------------}

-- | set callback function for receiving messages.
setLogger :: Solver -> (String -> IO ()) -> IO ()
setLogger solver logger = do
  writeIORef (mipLogger solver) (Just logger)

setOnUpdateBestSolution :: Solver -> (Model -> Rational -> IO ()) -> IO ()
setOnUpdateBestSolution solver cb = do
  writeIORef (mipOnUpdateBestSolution solver) cb

log :: Solver -> String -> IO ()
log solver msg = logIO solver (return msg)

logIO :: Solver -> IO String -> IO ()
logIO solver action = do
  m <- readIORef (mipLogger solver)
  case m of
    Nothing -> return ()
    Just logger -> action >>= logger

{--------------------------------------------------------------------
  GomoryCut
--------------------------------------------------------------------}

deriveGomoryCut :: Simplex.Solver -> IS.IntSet -> Var -> IO (LA.Atom Rational)
deriveGomoryCut lp ivs xi = do
  v0 <- Simplex.getValue lp xi
  let f0 = fracPart v0
  assert (0 < f0 && f0 < 1) $ return ()

  row <- Simplex.getRow lp xi

  -- remove fixed variables
  let p (_,xj) = do
        lb <- Simplex.getLB lp xj
        ub <- Simplex.getUB lp xj
        case (lb,ub) of
          (Just l, Just u) -> return (l < u)
          _ -> return True
  ns <- filterM p $ LA.terms row

  js <- flip filterM ns $ \(_, xj) -> do
    vj <- Simplex.getValue lp xj
    lb <- Simplex.getLB lp xj
    return $ Just vj == Simplex.boundValue lb
  ks <- flip filterM ns $ \(_, xj) -> do
    vj <- Simplex.getValue lp xj
    ub <- Simplex.getUB lp xj
    return $ Just vj == Simplex.boundValue ub

  xs1 <- forM js $ \(aij, xj) -> do
    let fj = fracPart aij
    Just (lj,_) <- Simplex.getLB lp xj
    let c = if xj `IS.member` ivs
            then (if fj <= 1 - f0 then fj  / (1 - f0) else ((1 - fj) / f0))
            else (if aij > 0      then aij / (1 - f0) else (-aij     / f0))
    return $ c *^ (LA.var xj ^-^ LA.constant lj)
  xs2 <- forM ks $ \(aij, xj) -> do
    let fj = fracPart aij
    Just (uj, _) <- Simplex.getUB lp xj
    let c = if xj `IS.member` ivs
            then (if fj <= f0 then fj  / f0 else ((1 - fj) / (1 - f0)))
            else (if aij > 0  then aij / f0 else (-aij     / (1 - f0)))
    return $ c *^ (LA.constant uj ^-^ LA.var xj)

  return $ sumV xs1 ^+^ sumV xs2 .>=. LA.constant 1

-- TODO: Simplexをδに対応させたら、xi, xj がδを含まない有理数であるという条件も必要
canDeriveGomoryCut :: Simplex.Solver -> Var -> IO Bool
canDeriveGomoryCut lp xi = do
  b <- Simplex.isBasicVariable lp xi
  if not b
    then return False
    else do
      val <- Simplex.getValue lp xi
      if isInteger val
        then return False
        else do
          row <- Simplex.getRow lp xi
          ys <- forM (LA.terms row) $ \(_,xj) -> do
            vj <- Simplex.getValue lp xj
            lb <- Simplex.getLB lp xj
            ub <- Simplex.getUB lp xj
            return $ Just vj == Simplex.boundValue lb || Just vj == Simplex.boundValue ub
          return (and ys)
