{-# Language BangPatterns #-}
{-# Language CPP #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.SLS.ProbSAT
-- Copyright   :  (c) Masahiro Sakai 2017
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- References:
--
----------------------------------------------------------------------
module ToySolver.SAT.SLS.ProbSAT
  ( Solver
  , newSolver
  , getNumVars
  , getRandGen
  , getBestSolution
  , getStatistics

  , Options (..)
  , Callbacks (..)
  , Statistics (..)

  , generateUniformRandomSolution

  , probsat
  , walksat
  ) where

import Prelude hiding (break)

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Data.Array.IArray
import Data.Array.IO
import Data.Array.Unboxed
import Data.Array.Unsafe
import Data.Default.Class
import qualified Data.Foldable as F
import Data.Int
import Data.IORef
import Data.Maybe
import Data.Sequence ((|>))
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import System.Clock
import qualified System.Random.MWC as Rand
import qualified System.Random.MWC.Distributions as Rand
import ToySolver.Internal.Data.IOURef
import qualified ToySolver.Internal.Data.Vec as Vec
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.Text.CNF as CNF

-- -------------------------------------------------------------------

data Solver
  = Solver
  { svClauses           :: !(Array Int PackedClause)
  , svOffset            :: !Int

  , svVarOccurs         :: !(Array SAT.Var (UArray Int ClauseId))
  , svVarOccursState    :: !(Array SAT.Var (IOArray Int VarOccurState))
  , svVarStateCounts    :: !(IOUArray (SAT.Var,VarOccurState) Int32)
  , svSolution          :: !(IOUArray SAT.Var Bool)

  , svClauseNumTrueLits    :: !(IOUArray ClauseId Int32)
  , svClauseVarOccursIndex :: !(Array ClauseId (Array Int Int))
  , svUnsatClauses         :: !(IORef (Set ClauseId))

  , svRandGen           :: !Rand.GenIO
  , svBestSolution      :: !(IORef (Int, SAT.Model))
  , svStatistics        :: !(IORef Statistics)
  }

type ClauseId = Int

type PackedClause = Array Int SAT.Lit

data VarOccurState
  = VOSMake
  | VOSBreak
  | VOSMakeBuf
  | VOSBreakBuf
  deriving (Eq, Ord, Enum, Bounded, Ix, Show)

newSolver :: CNF.CNF -> IO Solver
newSolver cnf = do
  let m :: SAT.Var -> Bool
      m _ = False

  offsetRef <- newIOURef (0::Int)
  cs <- liftM catMaybes $ forM (CNF.clauses cnf) $ \pc -> do
    case SAT.normalizeClause (SAT.unpackClause pc) of
      Nothing -> return Nothing
      Just [] -> modifyIOURef offsetRef inc >> return Nothing
      Just c  -> return $ Just $ listArray (0, length c - 1) c
  let clauses = listArray (0, length cs - 1) cs
  offset <- readIOURef offsetRef

  (varOccurs' :: IOArray SAT.Var (Seq.Seq (Int, VarOccurState))) <- newArray (1, CNF.numVars cnf) Seq.empty
  varStateCounts <- newArray ((1,minBound),(CNF.numVars cnf,maxBound)) 0

  clauseNumTrueLits <- newArray (bounds clauses) 0
  (clauseVarOccursIndex' :: IOArray ClauseId (Array Int Int)) <- newArray_ (bounds clauses)
  unsatClauses <- newIORef Set.empty

  forAssocsM_ clauses $ \(c,clause) -> do
    let n = sum [1 | lit <- elems clause, SAT.evalLit m lit]
    writeArray clauseNumTrueLits c n

    (idx :: IOUArray Int Int) <- newArray_ (bounds clause)

    if n == 0 then do
      modifyIORef' unsatClauses (Set.insert c)
      forAssocsM_ clause $ \(k,lit) -> do
        let v = SAT.litVar lit
        o <- readArray varOccurs' v
        writeArray idx k (Seq.length o)
        writeArray varOccurs' v (o |> (c,VOSMake))
        modifyArray varStateCounts (SAT.litVar lit, VOSMake) inc
    else if n == 1 then do
      forAssocsM_ clause $ \(k,lit) -> do
        let v = SAT.litVar lit
        o <- readArray varOccurs' v
        writeArray idx k (Seq.length o)
        if SAT.evalLit m lit then do
          writeArray varOccurs' v (o |> (c,VOSBreak))
          modifyArray varStateCounts (SAT.litVar lit, VOSBreak) inc
        else do
          writeArray varOccurs' v (o |> (c,VOSMakeBuf))
          modifyArray varStateCounts (SAT.litVar lit, VOSMakeBuf) inc
    else do
      forAssocsM_ clause $ \(k,lit) -> do
        let v = SAT.litVar lit
        o <- readArray varOccurs' v
        writeArray idx k (Seq.length o)
        if SAT.evalLit m lit then do
          writeArray varOccurs' v (o |> (c,VOSBreakBuf))
          modifyArray varStateCounts (SAT.litVar lit, VOSBreakBuf) inc
        else do
          writeArray varOccurs' v (o |> (c,VOSMakeBuf))
          modifyArray varStateCounts (SAT.litVar lit, VOSMakeBuf) inc

    writeArray clauseVarOccursIndex' c =<< unsafeFreeze idx

  varOccurs <- do
    (arr::IOArray SAT.Var (UArray Int ClauseId)) <- newArray_ (1, CNF.numVars cnf)
    forM_ [1 .. CNF.numVars cnf] $ \v -> do
      s <- readArray varOccurs' v
      writeArray arr v $ listArray (0, Seq.length s - 1) (map fst (F.toList s))
    unsafeFreeze arr

  varOccursState <- do
    (arr::IOArray SAT.Var (IOArray Int VarOccurState)) <- newArray_ (1, CNF.numVars cnf)
    forM_ [1 .. CNF.numVars cnf] $ \v -> do
      s <- readArray varOccurs' v
      ss <- newArray_ (0, Seq.length s - 1)
      forM_ (zip [0..] (F.toList s)) $ \(j,a) -> writeArray ss j (snd a)
      writeArray arr v ss
    unsafeFreeze arr

  clauseVarOccursIndex <- freeze clauseVarOccursIndex'

  solution <- newListArray (1, CNF.numVars cnf) $ [SAT.evalVar m v | v <- [1..CNF.numVars cnf]]

  bestObj <- liftM ((offset+) . Set.size) $ readIORef unsatClauses
  bestSol <- freeze solution
  bestSolution <- newIORef (bestObj, bestSol)

  randGen <- Rand.create

  stat <- newIORef def

  return $
    Solver
    { svClauses = clauses
    , svOffset = offset

    , svVarOccurs         = varOccurs
    , svVarOccursState    = varOccursState
    , svVarStateCounts    = varStateCounts
    , svSolution          = solution

    , svClauseNumTrueLits    = clauseNumTrueLits
    , svClauseVarOccursIndex = clauseVarOccursIndex
    , svUnsatClauses         = unsatClauses

    , svRandGen           = randGen
    , svBestSolution      = bestSolution
    , svStatistics        = stat
    }


flipVar :: Solver -> SAT.Var -> IO ()
flipVar solver v = do
  let occurs = svVarOccurs solver ! v
      occursState = svVarOccursState solver ! v
  seq occurs $ seq occursState $ return ()

  modifyArray (svSolution solver) v not

  forAssocsM_ occurs $ \(j,c) -> do
    let clause = svClauses solver ! c
        idx  = svClauseVarOccursIndex solver ! c
    s <- readArray occursState j

    case s of
      VOSMake -> do
        writeArray occursState j VOSBreak
        modifyArray (svVarStateCounts solver) (v, VOSMake) dec
        modifyArray (svVarStateCounts solver) (v, VOSBreak) inc
        modifyArray (svClauseNumTrueLits solver) c inc
        modifyIORef' (svUnsatClauses solver) (Set.delete c)
        forAssocsM_ clause $ \(k,lit) -> do
          let v2 = SAT.litVar lit
          unless (v == v2) $ do
            writeArray (svVarOccursState solver ! v2) (idx ! k) VOSMakeBuf
            modifyArray (svVarStateCounts solver) (v2, VOSMake) dec
            modifyArray (svVarStateCounts solver) (v2, VOSMakeBuf) inc
      VOSBreak -> do
        writeArray occursState j VOSMake
        modifyArray (svVarStateCounts solver) (v, VOSBreak) dec
        modifyArray (svVarStateCounts solver) (v, VOSMake) inc
        modifyArray (svClauseNumTrueLits solver) c dec
        modifyIORef' (svUnsatClauses solver) (Set.insert c)
        forAssocsM_ clause $ \(k,lit) -> do
          let v2 = SAT.litVar lit
          unless (v == v2) $ do
            writeArray (svVarOccursState solver ! v2) (idx ! k) VOSMake
            modifyArray (svVarStateCounts solver) (v2, VOSMakeBuf) dec
            modifyArray (svVarStateCounts solver) (v2, VOSMake) inc
      VOSMakeBuf -> do
        writeArray occursState j VOSBreakBuf
        modifyArray (svVarStateCounts solver) (v, VOSMakeBuf) dec
        modifyArray (svVarStateCounts solver) (v, VOSBreakBuf) inc
        modifyArray (svClauseNumTrueLits solver) c inc
        forAssocsM_ clause $ \(k,lit) -> do
          let v2 = SAT.litVar lit
          unless (v == v2) $ do
            s2 <- readArray (svVarOccursState solver ! v2) (idx ! k)
            when (s2 == VOSBreak) $ do
              writeArray (svVarOccursState solver ! v2) (idx ! k) VOSBreakBuf
              modifyArray (svVarStateCounts solver) (v2, VOSBreak) dec
              modifyArray (svVarStateCounts solver) (v2, VOSBreakBuf) inc
      VOSBreakBuf -> do
        writeArray occursState j VOSMakeBuf
        modifyArray (svVarStateCounts solver) (v, VOSBreakBuf) dec
        modifyArray (svVarStateCounts solver) (v, VOSMakeBuf) inc
        modifyArray (svClauseNumTrueLits solver) c dec
        n <- readArray (svClauseNumTrueLits solver) c
        when (n==1) $ do
          forAssocsM_ clause $ \(k,lit) -> do
            let v2 = SAT.litVar lit
            unless (v == v2) $ do
              s2 <- readArray (svVarOccursState solver ! v2) (idx ! k)
              when (s2 == VOSBreakBuf) $ do
                writeArray (svVarOccursState solver ! v2) (idx ! k) VOSBreak
                modifyArray (svVarStateCounts solver) (v2, VOSBreakBuf) dec
                modifyArray (svVarStateCounts solver) (v2, VOSBreak) inc

setSolution :: SAT.IModel m => Solver -> m -> IO ()
setSolution solver m = do
  b <- getBounds (svSolution solver)
  forM_ (range b) $ \v -> do
    val <- readArray (svSolution solver) v
    let val' = SAT.evalVar m v
    unless (val == val') $ do
      flipVar solver v

getNumVars :: Solver -> IO Int
getNumVars solver = return $ rangeSize $ bounds (svVarOccurs solver)

getRandGen :: Solver -> IO Rand.GenIO
getRandGen solver = return $ svRandGen solver

getBestSolution :: Solver -> IO (Int, SAT.Model)
getBestSolution solver = readIORef (svBestSolution solver)

getStatistics :: Solver -> IO Statistics
getStatistics solver = readIORef (svStatistics solver)

-- -------------------------------------------------------------------

data Options
  = Options
  { optTarget   :: !Int
  , optMaxTries :: !Int
  , optMaxFlips :: !Int
  }
  deriving (Eq, Show)

instance Default Options where
  def =
    Options
    { optTarget   = 0
    , optMaxTries = 1
    , optMaxFlips = 100000
    }

data Callbacks
  = Callbacks
  { cbGenerateInitialSolution :: Solver -> IO SAT.Model
  , cbOnUpdateBestSolution :: Solver -> Int -> SAT.Model -> IO ()
  }

instance Default Callbacks where
  def =
    Callbacks
    { cbGenerateInitialSolution = generateUniformRandomSolution
    , cbOnUpdateBestSolution = \_ _ _ -> return ()
    }

data Statistics
  = Statistics
  { statTotalCPUTime   :: !TimeSpec
  , statFlips          :: !Int
  , statFlipsPerSecond :: !Double
  }
  deriving (Eq, Show)

instance Default Statistics where
  def =
    Statistics
    { statTotalCPUTime = 0
    , statFlips = 0
    , statFlipsPerSecond = 0
    } 

-- -------------------------------------------------------------------

generateUniformRandomSolution :: Solver -> IO SAT.Model
generateUniformRandomSolution solver = do
  g <- getRandGen solver
  n <- getNumVars solver
  (a :: IOUArray Int Bool) <- newArray_ (1,n)
  forM_ [1..n] $ \v -> do
    b <- Rand.uniform g
    writeArray a v b
  unsafeFreeze a

checkCurrentSolution :: Solver -> Callbacks -> IO ()
checkCurrentSolution solver cb = do
  cs <- readIORef (svUnsatClauses solver)
  best <- readIORef (svBestSolution solver)
  let obj = Set.size cs + svOffset solver
  when (obj < fst best) $ do
    sol <- freeze (svSolution solver)
    writeIORef (svBestSolution solver) (obj, sol)
    cbOnUpdateBestSolution cb solver obj sol

-- -------------------------------------------------------------------

probsat :: Solver -> Options -> Callbacks -> (Double -> Double -> Double) -> IO ()
probsat solver opt cb f = do
  let maxClauseLen =
        if rangeSize (bounds (svClauses solver)) == 0
        then 0
        else maximum $ map (rangeSize . bounds) $ elems (svClauses solver)
  (wbuf :: IOUArray Int Double) <- newArray_ (0, maxClauseLen-1)
  wsumRef <- newIOURef (0 :: Double)

  let pickClause :: Set ClauseId -> IO PackedClause
      pickClause cs = do
        j <- Rand.uniformR (0, Set.size cs - 1) (svRandGen solver) -- For integral types inclusive range is used
        return $! (svClauses solver ! (Set.elemAt j cs))

      pickVar :: PackedClause -> IO SAT.Var
      pickVar c = do
        writeIOURef wsumRef 0
        forAssocsM_ c $ \(k,lit) -> do
          let v = SAT.litVar lit
          m <- readArray (svVarStateCounts solver) (v, VOSMake)
          b <- readArray (svVarStateCounts solver) (v, VOSBreak)
          let w = f (fromIntegral m) (fromIntegral b)
          writeArray wbuf k w
          modifyIOURef wsumRef (+w)
        wsum <- readIOURef wsumRef

        let go :: Int -> Double -> IO Int
            go !k !a = do
              if not (inRange (bounds c) k) then do
                return $! snd (bounds c)
              else do
                w <- readArray wbuf k
                if a <= w then
                  return k
                else
                  go (k + 1) (a - w)
        k <- go 0 =<< Rand.uniformR (0, wsum) (svRandGen solver)
        return $! SAT.litVar (c ! k)

  startCPUTime <- getTime ProcessCPUTime
  flipsRef <- newIOURef (0::Int)

  liftM (either id id) $ runExceptT $ do
    replicateM_ (optMaxTries opt) $ do
      lift $ do
        sol <- cbGenerateInitialSolution cb solver
        setSolution solver sol
        checkCurrentSolution solver cb
      replicateM_ (optMaxFlips opt) $ do
        cs <- lift $ readIORef (svUnsatClauses solver)
        when (Set.size cs <= optTarget opt) $ throwE ()
        lift $ do
          c <- pickClause cs
          v <- pickVar c
          flipVar solver v
          modifyIOURef flipsRef inc
          checkCurrentSolution solver cb

  endCPUTime <- getTime ProcessCPUTime
  flips <- readIOURef flipsRef
  let totalCPUTime = endCPUTime `diffTimeSpec` startCPUTime
      totalCPUTimeSec = fromIntegral (toNanoSecs totalCPUTime) / 10^(9::Int)
  writeIORef (svStatistics solver) $
    Statistics
    { statTotalCPUTime = totalCPUTime
    , statFlips = flips
    , statFlipsPerSecond = fromIntegral flips / totalCPUTimeSec
    }

  return ()



walksat :: Solver -> Options -> Callbacks -> Double -> IO ()
walksat solver opt cb p = do
  (buf :: Vec.UVec SAT.Var) <- Vec.new

  let pickClause :: Set ClauseId -> IO PackedClause
      pickClause cs = do
        j <- Rand.uniformR (0, Set.size cs - 1) (svRandGen solver) -- For integral types inclusive range is used
        return $! (svClauses solver ! (Set.elemAt j cs))

      pickVar :: PackedClause -> IO SAT.Var
      pickVar c = do
        liftM (either id id) $ runExceptT $ do
          let f :: Int32 -> SAT.Lit -> ExceptT SAT.Var IO Int32
              f b0 lit = do
                let v = SAT.litVar lit
                b <- lift $ readArray (svVarStateCounts solver) (v, VOSBreak)
                when (b == 0) $ throwE v -- freebie move
                return $! min b0 b
          b0 <- foldM f maxBound (elems c)
          lift $ do
            flag <- Rand.bernoulli p (svRandGen solver)
            if flag then do
              -- random walk move
              i <- Rand.uniformR (bounds c) (svRandGen solver)
              return $! SAT.litVar (c ! i)
            else do
              -- greedy move
              Vec.clear buf
              forM_ (elems c) $ \lit -> do
                let v = SAT.litVar lit
                b <- readArray (svVarStateCounts solver) (v, VOSBreak)
                when (b == b0) $ Vec.push buf v
              s <- Vec.getSize buf
              i <- Rand.uniformR (0, s - 1) (svRandGen solver)
              Vec.read buf i

  startCPUTime <- getTime ProcessCPUTime
  flipsRef <- newIOURef (0::Int)

  liftM (either id id) $ runExceptT $ do
    replicateM_ (optMaxTries opt) $ do
      lift $ do
        sol <- cbGenerateInitialSolution cb solver
        setSolution solver sol
        checkCurrentSolution solver cb
      replicateM_ (optMaxFlips opt) $ do
        cs <- lift $ readIORef (svUnsatClauses solver)
        when (Set.size cs <= optTarget opt) $ throwE ()
        lift $ do
          c <- pickClause cs
          v <- pickVar c
          flipVar solver v
          modifyIOURef flipsRef inc
          checkCurrentSolution solver cb

  endCPUTime <- getTime ProcessCPUTime
  flips <- readIOURef flipsRef
  let totalCPUTime = endCPUTime `diffTimeSpec` startCPUTime
      totalCPUTimeSec = fromIntegral (toNanoSecs totalCPUTime) / 10^(9::Int)
  writeIORef (svStatistics solver) $
    Statistics
    { statTotalCPUTime = totalCPUTime
    , statFlips = flips
    , statFlipsPerSecond = fromIntegral flips / totalCPUTimeSec
    }

  return ()

-- -------------------------------------------------------------------

{-# INLINE modifyArray #-}
modifyArray :: (MArray a e m, Ix i) => a i e -> i -> (e -> e) -> m ()
modifyArray a i f = do
  e <- readArray a i
  writeArray a i (f e)

{-# INLINE forAssocsM_ #-}
forAssocsM_ :: (Ix i, IArray a e, Monad m) => a i e -> ((i,e) -> m ()) -> m ()
forAssocsM_ a f = forM_ (assocs a) f
{-
forAssocsM_ a f =
  forM_ (range (bounds a)) $ \i -> do
    f (i, a ! i)
-}

{-# INLINE inc #-}
inc :: Integral a => a -> a
inc a = a+1

{-# INLINE dec #-}
dec :: Integral a => a -> a
dec a = a-1
             
-- -------------------------------------------------------------------
