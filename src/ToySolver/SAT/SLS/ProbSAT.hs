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
  , newSolverWeighted
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

import Control.Loop
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Data.Array.Base (unsafeRead, unsafeWrite, unsafeAt)
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
import System.Clock
import qualified System.Random.MWC as Rand
import qualified System.Random.MWC.Distributions as Rand
import ToySolver.Internal.Data.IOURef
import qualified ToySolver.Internal.Data.Vec as Vec
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.Text.CNF as CNF
import qualified ToySolver.Text.MaxSAT as MaxSAT

-- -------------------------------------------------------------------

data Solver
  = Solver
  { svClauses                :: !(Array ClauseId PackedClause)
  , svClauseWeights          :: !(Array ClauseId MaxSAT.Weight)
  , svClauseNumTrueLits      :: !(IOUArray ClauseId Int32)
  , svClauseUnsatClauseIndex :: !(IOUArray ClauseId Int)
  , svUnsatClauses           :: !(Vec.UVec ClauseId)

  , svVarOccurs         :: !(Array SAT.Var (UArray Int ClauseId))
  , svVarOccursState    :: !(Array SAT.Var (IOUArray Int Bool))
  , svSolution          :: !(IOUArray SAT.Var Bool)

  , svObj               :: !(IORef MaxSAT.Weight)

  , svRandGen           :: !Rand.GenIO
  , svBestSolution      :: !(IORef (MaxSAT.Weight, SAT.Model))
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
  let wcnf =
        MaxSAT.WCNF
        { MaxSAT.numVars    = CNF.numVars cnf
        , MaxSAT.numClauses = CNF.numClauses cnf
        , MaxSAT.topCost    = fromIntegral (CNF.numClauses cnf) + 1
        , MaxSAT.clauses    = [(1,c) | c <- CNF.clauses cnf]
        }
  newSolverWeighted wcnf

newSolverWeighted :: MaxSAT.WCNF -> IO Solver
newSolverWeighted wcnf = do
  let m :: SAT.Var -> Bool
      m _ = False
      nv = MaxSAT.numVars wcnf

  objRef <- newIORef (0::Integer)

  cs <- liftM catMaybes $ forM (MaxSAT.clauses wcnf) $ \(w,pc) -> do
    case SAT.normalizeClause (SAT.unpackClause pc) of
      Nothing -> return Nothing
      Just [] -> modifyIORef' objRef (w+) >> return Nothing
      Just c  -> do
        let c' = listArray (0, length c - 1) c
        seq c' $ return (Just (w,c'))
  let len = length cs
      clauses  = listArray (0, len - 1) (map snd cs)
      weights  :: Array ClauseId MaxSAT.Weight
      weights  = listArray (0, len - 1) (map fst cs)

  (varOccurs' :: IOArray SAT.Var (Seq.Seq (Int, Bool))) <- newArray (1, nv) Seq.empty

  clauseNumTrueLits <- newArray (bounds clauses) 0
  clauseUnsatClauseIndex <- newArray (bounds clauses) (-1)
  unsatClauses <- Vec.new

  forAssocsM_ clauses $ \(c,clause) -> do
    let n = sum [1 | lit <- elems clause, SAT.evalLit m lit]
    writeArray clauseNumTrueLits c n
    when (n == 0) $ do
      i <- Vec.getSize unsatClauses
      writeArray clauseUnsatClauseIndex c i
      Vec.push unsatClauses c
      modifyIORef objRef ((weights ! c) +)
    forM_ (elems clause) $ \lit -> do
      let v = SAT.litVar lit
      let b = SAT.evalLit m lit
      seq b $ modifyArray varOccurs' v (|> (c,b))

  varOccurs <- do
    (arr::IOArray SAT.Var (UArray Int ClauseId)) <- newArray_ (1, nv)
    forM_ [1 .. nv] $ \v -> do
      s <- readArray varOccurs' v
      writeArray arr v $ listArray (0, Seq.length s - 1) (map fst (F.toList s))
    unsafeFreeze arr

  varOccursState <- do
    (arr::IOArray SAT.Var (IOUArray Int Bool)) <- newArray_ (1, nv)
    forM_ [1 .. nv] $ \v -> do
      s <- readArray varOccurs' v
      ss <- newArray_ (0, Seq.length s - 1)
      forM_ (zip [0..] (F.toList s)) $ \(j,a) -> writeArray ss j (snd a)
      writeArray arr v ss
    unsafeFreeze arr

  solution <- newListArray (1, nv) $ [SAT.evalVar m v | v <- [1..nv]]

  bestObj <- readIORef objRef
  bestSol <- freeze solution
  bestSolution <- newIORef (bestObj, bestSol)

  randGen <- Rand.create

  stat <- newIORef def

  return $
    Solver
    { svClauses = clauses
    , svClauseWeights          = weights
    , svClauseNumTrueLits      = clauseNumTrueLits
    , svClauseUnsatClauseIndex = clauseUnsatClauseIndex
    , svUnsatClauses           = unsatClauses

    , svVarOccurs         = varOccurs
    , svVarOccursState    = varOccursState
    , svSolution          = solution

    , svObj = objRef

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
  forAssocsM_ occurs $ \(j,!c) -> do
    b <- unsafeRead occursState j
    n <- unsafeRead (svClauseNumTrueLits solver) c
    unsafeWrite occursState j (not b)
    if b then do
      unsafeWrite (svClauseNumTrueLits solver) c (n-1)
      when (n==1) $ do
        i <- Vec.getSize (svUnsatClauses solver)
        Vec.push (svUnsatClauses solver) c
        unsafeWrite (svClauseUnsatClauseIndex solver) c i
        modifyIORef' (svObj solver) (+ unsafeAt (svClauseWeights solver) c)
    else do
      unsafeWrite (svClauseNumTrueLits solver) c (n+1)
      when (n==0) $ do
        s <- Vec.getSize (svUnsatClauses solver)
        i <- unsafeRead (svClauseUnsatClauseIndex solver) c
        unless (i == s-1) $ do
          let i2 = s-1
          c2 <- Vec.read (svUnsatClauses solver) i2
          Vec.write (svUnsatClauses solver) i2 c
          Vec.write (svUnsatClauses solver) i c2
          unsafeWrite (svClauseUnsatClauseIndex solver) c2 i
        _ <- Vec.unsafePop (svUnsatClauses solver)
        modifyIORef' (svObj solver) (subtract (unsafeAt (svClauseWeights solver) c))
        return ()

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

getBestSolution :: Solver -> IO (MaxSAT.Weight, SAT.Model)
getBestSolution solver = readIORef (svBestSolution solver)

getStatistics :: Solver -> IO Statistics
getStatistics solver = readIORef (svStatistics solver)

{-# INLINE getMakeValue #-}
getMakeValue :: Solver -> SAT.Var -> IO Int
getMakeValue solver v = do
  let occurs = svVarOccurs solver ! v
      (lb,ub) = bounds occurs
  seq occurs $ seq lb $ seq ub $
    numLoopState lb ub 0 $ \ !r !i -> do
      n <- unsafeRead (svClauseNumTrueLits solver) (unsafeAt occurs i)
      return $! if n == 0 then (r+1) else r

{-# INLINE getBreakValue #-}
getBreakValue :: Solver -> SAT.Var -> IO Int
getBreakValue solver v = do
  let occurs = svVarOccurs solver ! v
      occursState = svVarOccursState solver ! v
      (lb,ub) = bounds occurs
  seq occurs $ seq occursState $ seq lb $ seq ub $
    numLoopState lb ub 0 $ \ !r !i -> do
      b <- unsafeRead occursState i
      if b then do
        n <- unsafeRead (svClauseNumTrueLits solver) (unsafeAt occurs i)
        return $! if n==1 then (r+1) else r
      else
        return r

-- -------------------------------------------------------------------

data Options
  = Options
  { optTarget   :: !MaxSAT.Weight
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
  , cbOnUpdateBestSolution :: Solver -> MaxSAT.Weight -> SAT.Model -> IO ()
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
  best <- readIORef (svBestSolution solver)
  obj <- readIORef (svObj solver)
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

  let pickClause :: IO PackedClause
      pickClause = do
        s <- Vec.getSize (svUnsatClauses solver)
        j <- Rand.uniformR (0, s - 1) (svRandGen solver) -- For integral types inclusive range is used
        liftM (svClauses solver !) $ Vec.read (svUnsatClauses solver) j

      pickVar :: PackedClause -> IO SAT.Var
      pickVar c = do
        writeIOURef wsumRef 0
        forAssocsM_ c $ \(k,lit) -> do
          let v = SAT.litVar lit
          m <- getMakeValue solver v
          b <- getBreakValue solver v
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
        s <- lift $ Vec.getSize (svUnsatClauses solver)
        when (s == 0) $ throwE ()
        obj <- lift $ readIORef (svObj solver)
        when (obj <= optTarget opt) $ throwE ()
        lift $ do
          c <- pickClause
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
  (breaks :: Vec.UVec Int) <- Vec.new

  let pickClause :: IO PackedClause
      pickClause = do
        s <- Vec.getSize (svUnsatClauses solver)
        j <- Rand.uniformR (0, s - 1) (svRandGen solver) -- For integral types inclusive range is used
        liftM (svClauses solver !) $ Vec.read (svUnsatClauses solver) j

      pickVar :: PackedClause -> IO SAT.Var
      pickVar c = do
        liftM (either id id) $ runExceptT $ do
          lift $ Vec.clear breaks
          let (lb,ub) = bounds c
          b0 <- numLoopState lb ub maxBound $ \ !b0 !i -> do
            let v = SAT.litVar (c ! i)
            b <- lift $ getBreakValue solver v
            when (b == 0) $ throwE v -- freebie move
            lift $ Vec.push breaks b
            return $! min b0 b
          lift $ do
            flag <- Rand.bernoulli p (svRandGen solver)
            if flag then do
              -- random walk move
              i <- Rand.uniformR (bounds c) (svRandGen solver)
              return $! SAT.litVar (c ! i)
            else do
              -- greedy move
              Vec.clear buf
              forAssocsM_ c $ \(i,!lit) -> do
                b <- Vec.read breaks i
                when (b == b0) $ Vec.push buf (SAT.litVar lit)
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
        obj <- lift $ readIORef (svObj solver)
        when (obj <= optTarget opt) $ throwE ()
        lift $ do
          c <- pickClause
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
forAssocsM_ :: (IArray a e, Monad m) => a Int e -> ((Int,e) -> m ()) -> m ()
forAssocsM_ a f = do
  let (lb,ub) = bounds a
  numLoop lb ub $ \i ->
    f (i, unsafeAt a i)

{-# INLINE inc #-}
inc :: Integral a => a -> a
inc a = a+1
             
-- -------------------------------------------------------------------
