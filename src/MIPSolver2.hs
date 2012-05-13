{-# LANGUAGE ScopedTypeVariables, Rank2Types #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  MIPSolver2
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Naïve implementation of MIP solver based on Simplex2 module
-- 
-- Reference:
--
-- * <http://www.math.cuhk.edu.hk/~wei/lpch3.pdf>
-- 
-- * R. C. Daniel and Martyn Jeffreys.
--   "Unboundedness in Integer and Discrete Programming L.P. Relaxations"
--   The Journal of the Operational Research Society, Vol. 30, No. 12. (1979)
--   <http://www.jstor.org/stable/3009435>
-- 
-----------------------------------------------------------------------------
module MIPSolver2
  (
  -- * The @Solver@ type
    Solver
  , newSolver

  -- * Solving
  , optimize

  -- * Extract results
  , model
  , getObjValue

  -- * Configulation
  , setNThread
  , setLogger
  , setShowRational
  ) where

import Prelude hiding (log)

import Control.Monad
import Control.Exception
import Control.Concurrent
import Control.Concurrent.STM
import Data.List
import Data.OptDir
import Data.Ord
import Data.IORef
import Data.Maybe
import Data.Ratio
import qualified Data.IntSet as IS
import qualified Data.IntMap as IM
import qualified Data.Set as Set
import qualified Data.Sequence as Seq
import System.CPUTime
import Text.Printf

import qualified LA
import Formula ((.<=.), (.>=.), (.==.))
import qualified Simplex2
import Simplex2 (OptResult (..), Var, Model)
import qualified OmegaTest
import Linear
import Util (isInteger, fracPart)

data Solver
  = MIP
  { mipRootLP :: Simplex2.Solver
  , mipIVs    :: IS.IntSet
  , mipBest   :: IORef (Maybe (Node, Rational))

  , mipNThread :: IORef Int
  , mipLogger  :: IORef (Maybe (String -> IO ()))
  , mipShowRational :: IORef Bool
  }

data Node =
  Node
  { ndLP    :: Simplex2.Solver
  , ndDepth :: {-# UNPACK #-} !Int
  }

newSolver :: Simplex2.Solver -> IS.IntSet -> IO Solver
newSolver lp ivs = do
  lp2 <- Simplex2.cloneSolver lp

  forM_ (IS.toList ivs) $ \v -> do
    lb <- Simplex2.getLB lp2 v
    case lb of
      Just l | not (isInteger l) ->
        Simplex2.assertLower lp2 v (fromInteger (ceiling l))
      _ -> return ()
    ub <- Simplex2.getUB lp2 v
    case ub of
      Just u | not (isInteger u) ->
        Simplex2.assertLower lp2 v (fromInteger (floor u))
      _ -> return ()

  bestRef <- newIORef Nothing

  nthreadRef <- newIORef 0
  logRef  <- newIORef Nothing
  showRef <- newIORef False

  return $
    MIP
    { mipRootLP = lp2
    , mipIVs    = ivs
    , mipBest   = bestRef

    , mipNThread = nthreadRef
    , mipLogger = logRef
    , mipShowRational = showRef
    }

optimize :: Solver -> (Model -> Rational -> IO ()) -> IO OptResult
optimize solver update = do
  let lp = mipRootLP solver
  log solver "MIP: Solving LP relaxation..."
  ret <- Simplex2.check lp
  if not ret
  then return Unsat
  else do
    s0 <- showValue solver =<< Simplex2.getObjValue lp
    log solver (printf "MIP: LP relaxation is satisfiable with obj = %s" s0)
    log solver "MIP: Optimizing LP relaxation"
    ret2 <- Simplex2.optimize lp
    case ret2 of
      Unsat -> error "should not happen"
      Unbounded -> do
        log solver "MIP: LP relaxation is unbounded"
        let ivs = mipIVs solver
        if IS.null ivs
          then return Unbounded
          else do
            {-
              Fallback to Fourier-Motzkin + OmegaTest
              * In general, original problem may have optimal
                solution even though LP relaxiation is unbounded.
              * But if restricted to rational numbers, the
                original problem is unbounded or unsatisfiable
                when LP relaxation is unbounded.
            -}
            log solver "MIP: falling back to Fourier-Motzkin + OmegaTest"
            t <- Simplex2.getTableau lp
            let ds = [LA.varExpr v .==. def | (v, def) <- IM.toList t]
            n <- Simplex2.nVars lp
            bs <- liftM concat $ forM [0..n-1] $ \v -> do
              lb <- Simplex2.getLB lp v
              ub <- Simplex2.getUB lp v
              return $ [LA.varExpr v .>=. LA.constExpr (fromJust lb) | isJust lb] ++
                       [LA.varExpr v .<=. LA.constExpr (fromJust ub) | isJust ub]
            case OmegaTest.solveQFLA (bs ++ ds) ivs of
              Just _ -> return Unbounded
              Nothing -> return Unsat  
      Optimum -> do
        s0 <- showValue solver =<< Simplex2.getObjValue lp
        log solver $ "MIP: LP relaxation optimum is " ++ s0
        log solver "MIP: Integer optimization begins..."
        Simplex2.clearLogger lp
        branchAndBound solver update
        m <- readIORef (mipBest solver)
        case m of
          Nothing -> return Unsat
          Just _ -> return Optimum

branchAndBound :: Solver -> (Model -> Rational -> IO ()) -> IO ()
branchAndBound solver update = do
  let root = Node{ ndLP = mipRootLP solver, ndDepth = 0 }

  pool <- newTVarIO (Seq.singleton root)
  activeThreads <- newTVarIO (Set.empty)

  let addNode :: Node -> IO ()
      addNode nd = atomically $ do
        modifyTVar pool (Seq.|> nd)

      pickNode :: IO (Maybe Node)
      pickNode = do
        self <- myThreadId
        atomically $ modifyTVar activeThreads (Set.delete self)
        atomically $ do
          s <- readTVar pool
          case Seq.viewl s of
            nd Seq.:< s2 -> do
              writeTVar pool s2
              modifyTVar activeThreads (Set.insert self)
              return (Just nd)
            Seq.EmptyL -> do
              ths <- readTVar activeThreads
              if Set.null ths
                then return Nothing
                else retry

      updateBest :: Node -> Rational -> IO ()
      updateBest node val = do
        let lp = ndLP node
        m <- Simplex2.model lp
        dir <- Simplex2.getOptDir lp
        ret <- atomicModifyIORef (mipBest solver) $ \old -> do
          case old of
            Nothing -> (Just (node, val), True)
            Just (_, best) -> do
              let isBetter = if dir==OptMin then val < best else val > best
              if isBetter
                then (Just (node, val), True)
                else (old, False)
        when ret $ update m val -- 複数スレッドからupdateが同時に呼ばれてまずい可能性がある

      processNode :: Node -> IO ()
      processNode node = do
        let lp = ndLP node
        ret <- Simplex2.dualSimplex lp
        case ret of
          Unbounded -> error "should not happen"
          Unsat ->  return ()
          Optimum -> do
            val <- Simplex2.getObjValue lp
            p <- prune solver val
            unless p $ do
              xs <- violated node (mipIVs solver)
              case xs of
                [] -> updateBest node val
                _ -> do
                  r <- if ndDepth node `mod` 100 /= 0
                       then return Nothing
                       else liftM listToMaybe $ filterM (canDeriveGomoryCut lp) $ map fst xs
                  case r of
                    Nothing -> do -- branch
                      let (v0,val0) = fst $ maximumBy (comparing snd)
                                      [((v,val), abs (fromInteger (round val) - val)) | (v,val) <- xs]
                      let lp1 = lp
                      lp2 <- Simplex2.cloneSolver lp
                      Simplex2.assertAtom lp1 (LA.varExpr v0 .<=. LA.constExpr (fromInteger (floor val0)))
                      addNode $ Node lp1 (ndDepth node + 1)
                      Simplex2.assertAtom lp2 (LA.varExpr v0 .>=. LA.constExpr (fromInteger (ceiling val0)))
                      addNode $ Node lp2 (ndDepth node + 1)
                    Just v -> do -- cut
                      atom <- deriveGomoryCut lp (mipIVs solver) v
                      Simplex2.assertAtom lp atom
                      addNode $ Node lp (ndDepth node + 1)

  let isCompleted = do
        nodes <- readTVar pool
        threads <- readTVar activeThreads
        return $ Seq.null nodes && Set.null threads

  -- fork worker threads
  nthreads <- do
    n <- readIORef (mipNThread solver)
    if n >= 1
      then return n
      else return 1 -- getNumCapabilities -- base-4.4.0.0以降にしか存在しない

  let child = do
        m <- pickNode
        case m of
          Nothing -> return ()
          Just node -> processNode node >> child

  log solver $ printf "MIP: forking %d worker threads..." nthreads
  start <- getCPUTime
  ex <- newEmptyTMVarIO
  threads <- replicateM nthreads $ do
    mask $ \restore -> forkIO $ do
      ret <- try (restore child)
      case ret of
        Left e -> atomically (putTMVar ex e)
        Right _ -> return ()

  th <- forkIO $ do
    let loop = do
          n <- atomically $ do
            nodes   <- readTVar pool
            athreads <- readTVar activeThreads
            return (Seq.length nodes + Set.size athreads)
          if n == 0
            then return ()
            else do
              now <- getCPUTime
              let spent = (now - start) `div` 10^(12::Int)
              log solver $ printf "time = %d sec; nodes: %d" spent n
              threadDelay (2*1000*1000) -- 2s
              loop
    loop

  -- join
  let wait = isCompleted >>= guard >> return Nothing
  let loop :: (forall a. IO a -> IO a) -> IO ()
      loop restore = do
        ret <- try $ restore $ atomically $ wait `orElse` (liftM Just (readTMVar ex))
        case ret of
          Right Nothing  -> return ()
          Right (Just (e::SomeException)) -> do
            mapM_ (\t -> throwTo t e) (th:threads)
            throwIO e
          Left (e::SomeException) -> do
            mapM_ (\t -> throwTo t e) (th:threads)
            throwIO e
  mask loop

model :: Solver -> IO Model
model solver = do
  m <- readIORef (mipBest solver)
  case m of
    Nothing -> error "no model"
    Just (node,_) -> Simplex2.model (ndLP node)

getObjValue :: Solver -> IO Rational
getObjValue solver = do
  m <- readIORef (mipBest solver)
  case m of
    Nothing -> error "no model"
    Just (_,val) -> return val

violated :: Node -> IS.IntSet -> IO [(Var, Rational)]
violated node ivs = do
  m <- Simplex2.model (ndLP node)
  let p (v,val) = v `IS.member` ivs && not (isInteger val)
  return $ filter p (IM.toList m)

prune :: Solver -> Rational -> IO Bool
prune solver lb = do
  b <- readIORef (mipBest solver)
  case b of
    Nothing -> return False
    Just (_, best) -> do
      dir <- Simplex2.getOptDir (mipRootLP solver)
      return $ if dir==OptMin then best <= lb else best >= lb

showValue :: Solver -> Rational -> IO String
showValue solver v
  | denominator v == 1 = return $ show (numerator v)
  | otherwise = do
      printRat <- readIORef (mipShowRational solver)
      if printRat
        then return $ show (numerator v) ++ "/" ++ show (denominator v)
        else return $ show (fromRational v :: Double)

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

deriveGomoryCut :: Simplex2.Solver -> IS.IntSet -> Var -> IO (LA.Atom Rational)
deriveGomoryCut lp ivs xi = do
  v0 <- Simplex2.getValue lp xi
  let f0 = fracPart v0
  assert (0 < f0 && f0 < 1) $ return ()

  row <- Simplex2.getRow lp xi

  -- remove fixed variables
  let p (_,xj) = do
        lb <- Simplex2.getLB lp xj
        ub <- Simplex2.getUB lp xj
        case (lb,ub) of
          (Just l, Just u) -> return (l < u)
          _ -> return True
  ns <- filterM p $ LA.terms row

  js <- flip filterM ns $ \(_, xj) -> do
    vj <- Simplex2.getValue lp xj
    lb <- Simplex2.getLB lp xj
    return $ Just vj == lb
  ks <- flip filterM ns $ \(_, xj) -> do
    vj <- Simplex2.getValue lp xj
    ub <- Simplex2.getUB lp xj
    return $ Just vj == ub

  xs1 <- forM js $ \(aij, xj) -> do
    vj <- Simplex2.getValue lp xj
    let fj = fracPart vj
    Just lj <- Simplex2.getLB lp xj
    let c = if xj `IS.member` ivs
            then (if fj <= 1 - f0 then fj  / (1 - f0) else ((1 - fj) / f0))
            else (if aij > 0      then aij / (1 - f0) else (-aij     / f0))
    return $ c .*. (LA.varExpr xj .-. LA.constExpr lj)
  xs2 <- forM ks $ \(aij, xj) -> do
    vj <- Simplex2.getValue lp xj
    let fj = fracPart vj
    Just uj <- Simplex2.getUB lp xj
    let c = if xj `IS.member` ivs
            then (if fj <= f0 then fj  / f0 else ((1 - fj) / (1 - f0)))
            else (if aij > 0  then aij / f0 else (-aij     / (1 - f0)))
    return $ c .*. (LA.constExpr uj .-. LA.varExpr xj)

  return $ lsum xs1 .+. lsum xs2 .>=. LA.constExpr 1

-- TODO: Simplex2をδに対応させたら、xi, xj がδを含まない有理数であるという条件も必要
canDeriveGomoryCut :: Simplex2.Solver -> Var -> IO Bool
canDeriveGomoryCut lp xi = do
  b <- Simplex2.isBasicVariable lp xi
  if not b
    then return False
    else do
      val <- Simplex2.getValue lp xi
      if isInteger val
        then return False
        else do
          row <- Simplex2.getRow lp xi
          ys <- forM (LA.terms row) $ \(_,xj) -> do
            vj <- Simplex2.getValue lp xj
            lb <- Simplex2.getLB lp xj
            ub <- Simplex2.getUB lp xj
            return $ Just vj == lb || Just vj == ub
          return (and ys)
