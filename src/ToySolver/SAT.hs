{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
{-# LANGUAGE BangPatterns, ScopedTypeVariables, CPP, DeriveDataTypeable #-}
#ifdef __GLASGOW_HASKELL__
{-# LANGUAGE UnboxedTuples, MagicHash #-}
#endif
#if __GLASGOW_HASKELL__ < 706
{-# LANGUAGE DoRec #-}
#else
{-# LANGUAGE RecursiveDo #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (BangPatterns, ScopedTypeVariables, CPP, DeriveDataTypeable, RecursiveDo)
--
-- A CDCL SAT solver.
--
-- It follows the design of MiniSat and SAT4J.
--
-- See also:
--
-- * <http://hackage.haskell.org/package/funsat>
--
-- * <http://hackage.haskell.org/package/incremental-sat-solver>
--
-----------------------------------------------------------------------------
module ToySolver.SAT
  (
  -- * The @Solver@ type
    Solver
  , newSolver

  -- * Basic data structures
  , Var
  , Lit
  , literal
  , litNot
  , litVar
  , litPolarity
  , Clause

  -- * Problem specification
  , newVar
  , newVars
  , newVars_
  , resizeVarCapacity
  , addClause
  , addAtLeast
  , addAtMost
  , addExactly
  , addPBAtLeast
  , addPBAtMost
  , addPBExactly
  , addPBAtLeastSoft
  , addPBAtMostSoft
  , addPBExactlySoft

  -- * Solving
  , solve
  , solveWith
  , BudgetExceeded (..)

  -- * Extract results
  , Model
  , model
  , failedAssumptions

  -- * Solver configulation
  , RestartStrategy (..)
  , setRestartStrategy
  , defaultRestartStrategy
  , setRestartFirst
  , defaultRestartFirst
  , setRestartInc
  , defaultRestartInc
  , setLearntSizeFirst
  , defaultLearntSizeFirst
  , setLearntSizeInc
  , defaultLearntSizeInc
  , setCCMin
  , defaultCCMin
  , LearningStrategy (..)
  , setLearningStrategy
  , defaultLearningStrategy
  , setEnablePhaseSaving
  , getEnablePhaseSaving
  , defaultEnablePhaseSaving
  , setEnableForwardSubsumptionRemoval
  , getEnableForwardSubsumptionRemoval
  , defaultEnableForwardSubsumptionRemoval
  , setEnableBackwardSubsumptionRemoval
  , getEnableBackwardSubsumptionRemoval
  , defaultEnableBackwardSubsumptionRemoval
  , setVarPolarity
  , setLogger
  , setCheckModel
  , setRandomFreq
  , defaultRandomFreq
  , setRandomGen
  , getRandomGen
  , setConfBudget
  , PBHandlerType (..)
  , setPBHandlerType
  , defaultPBHandlerType

  -- * Read state
  , nVars
  , nAssigns
  , nConstraints
  , nLearnt

  -- * Internal API
  , varBumpActivity
  , varDecayActivity
  ) where

import Prelude hiding (log)
import Control.Loop
import Control.Monad
import Control.Exception
#if MIN_VERSION_array(0,5,0)
import Data.Array.IO
#else
import Data.Array.IO hiding (unsafeFreeze)
#endif
import Data.Array.Unsafe (unsafeFreeze)
import Data.Array.Base (unsafeRead, unsafeWrite)
#if MIN_VERSION_hashable(1,2,0)
import Data.Bits (xor) -- for defining 'combine' function
#endif
import Data.Function (on)
import Data.Hashable
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.IORef
import Data.List
import Data.Maybe
import Data.Ord
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Set as Set
import qualified ToySolver.Internal.Data.IndexedPriorityQueue as PQ
import qualified ToySolver.Internal.Data.SeqQueue as SQ
import qualified ToySolver.Internal.Data.Vec as Vec
import Data.Time
import Data.Typeable
import System.CPUTime
import qualified System.Random as Rand
import Text.Printf

#ifdef __GLASGOW_HASKELL__
import GHC.Types (IO (..))
import GHC.Exts hiding (Constraint)
#endif

import ToySolver.Data.LBool
import ToySolver.SAT.Types

{--------------------------------------------------------------------
  internal data structures
--------------------------------------------------------------------}

type Level = Int

levelRoot :: Level
levelRoot = -1

data Assignment
  = Assignment
  { aValue  :: !Bool
  , aIndex  :: {-# UNPACK #-} !Int
  , aLevel  :: {-# UNPACK #-} !Level
  , aReason :: !(Maybe SomeConstraintHandler)
  , aBacktrackCBs :: !(IORef [IO ()])
  }

data VarData
  = VarData
  { vdAssignment :: !(IORef (Maybe Assignment))
  , vdPolarity   :: !(IORef Bool)
  , vdPosLitData :: !LitData
  , vdNegLitData :: !LitData
  -- | will be invoked when the variable is assigned
  , vdWatches    :: !(IORef [SomeConstraintHandler])
  , vdActivity   :: !(IORef VarActivity)
  }

data LitData
  = LitData
  { -- | will be invoked when this literal is falsified
    ldWatches   :: !(IORef [SomeConstraintHandler])
  , ldOccurList :: !(IORef (HashSet SomeConstraintHandler))
  }

newVarData :: IO VarData
newVarData = do
  ainfo <- newIORef Nothing
  polarity <- newIORef True
  pos <- newLitData
  neg <- newLitData
  watches <- newIORef []
  activity <- newIORef 0
  return $ VarData ainfo polarity pos neg watches activity

newLitData :: IO LitData
newLitData = do
  ws <- newIORef []
  occ <- newIORef HashSet.empty
  return $ LitData ws occ

varData :: Solver -> Var -> IO VarData
varData solver !v = Vec.unsafeRead (svVarData solver) (v-1)

litData :: Solver -> Lit -> IO LitData
litData solver !l =
  -- litVar による heap allocation を避けるために、
  -- litPolarityによる分岐後にvarDataを呼ぶ。
  if litPolarity l then do
    vd <- varData solver l
    return $ vdPosLitData vd
  else do
    vd <- varData solver (negate l)
    return $ vdNegLitData vd

{-# INLINE varValue #-}
varValue :: Solver -> Var -> IO LBool
varValue solver !v = do
  vd <- varData solver v
  m <- readIORef (vdAssignment vd)
  case m of
    Nothing -> return lUndef
    Just x -> return $! (liftBool $! aValue x)

{-# INLINE litValue #-}
litValue :: Solver -> Lit -> IO LBool
litValue solver !l = do
  -- litVar による heap allocation を避けるために、
  -- litPolarityによる分岐後にvarDataを呼ぶ。
  if litPolarity l then
    varValue solver l
  else do
    m <- varValue solver (negate l)
    return $! lnot m

varLevel :: Solver -> Var -> IO Level
varLevel solver !v = do
  vd <- varData solver v
  m <- readIORef (vdAssignment vd)
  case m of
    Nothing -> error ("ToySolver.SAT.varLevel: unassigned var " ++ show v)
    Just a -> return (aLevel a)

litLevel :: Solver -> Lit -> IO Level
litLevel solver l = varLevel solver (litVar l)

varReason :: Solver -> Var -> IO (Maybe SomeConstraintHandler)
varReason solver !v = do
  vd <- varData solver v
  m <- readIORef (vdAssignment vd)
  case m of
    Nothing -> error ("ToySolver.SAT.varReason: unassigned var " ++ show v)
    Just a -> return (aReason a)

varAssignNo :: Solver -> Var -> IO Int
varAssignNo solver !v = do
  vd <- varData solver v
  m <- readIORef (vdAssignment vd)
  case m of
    Nothing -> error ("ToySolver.SAT.varAssignNo: unassigned var " ++ show v)
    Just a -> return (aIndex a)

-- | Solver instance
data Solver
  = Solver
  { svOk           :: !(IORef Bool)
  , svVarQueue     :: !PQ.PriorityQueue
  , svTrail        :: !(IORef [Lit])
  , svVarData      :: !(Vec.Vec VarData)
  , svConstrDB     :: !(IORef [SomeConstraintHandler])
  , svLearntDB     :: !(IORef (Int,[SomeConstraintHandler]))
  , svAssumptions  :: !(IORef (IOUArray Int Lit))
  , svLevel        :: !(IORef Level)
  , svBCPQueue     :: !(SQ.SeqQueue Lit)
  , svModel        :: !(IORef (Maybe Model))
  , svNDecision    :: !(IORef Int)
  , svNRandomDecision :: !(IORef Int)
  , svNConflict    :: !(IORef Int)
  , svNRestart     :: !(IORef Int)
  , svNAssigns     :: !(IORef Int)
  , svNFixed       :: !(IORef Int)
  , svNLearntGC    :: !(IORef Int)
  , svNRemovedConstr :: !(IORef Int)

  -- | Inverse of the variable activity decay factor. (default 1 / 0.95)
  , svVarDecay     :: !(IORef Double)

  -- | Amount to bump next variable with.
  , svVarInc       :: !(IORef Double)

  -- | Inverse of the constraint activity decay factor. (1 / 0.999)
  , svConstrDecay  :: !(IORef Double)

  -- | Amount to bump next constraint with.
  , svConstrInc    :: !(IORef Double)

  , svRestartStrategy :: !(IORef RestartStrategy)

  -- | The initial restart limit. (default 100)
  , svRestartFirst :: !(IORef Int)

  -- | The factor with which the restart limit is multiplied in each restart. (default 1.5)
  , svRestartInc :: !(IORef Double)

  -- | The initial limit for learnt constraints.
  , svLearntSizeFirst :: !(IORef Int)

  -- | The limit for learnt constraints is multiplied with this factor periodically. (default 1.1)
  , svLearntSizeInc :: !(IORef Double)

  , svLearntLim       :: !(IORef Int)
  , svLearntLimAdjCnt :: !(IORef Int)
  , svLearntLimSeq    :: !(IORef [(Int,Int)])

  -- | Controls conflict constraint minimization (0=none, 1=local, 2=recursive)
  , svCCMin :: !(IORef Int)

  , svEnablePhaseSaving :: !(IORef Bool)
  , svEnableForwardSubsumptionRemoval :: !(IORef Bool)

  , svLearningStrategy :: !(IORef LearningStrategy)

  , svPBHandlerType :: !(IORef PBHandlerType)

  , svEnableBackwardSubsumptionRemoval :: !(IORef Bool)

  , svLogger :: !(IORef (Maybe (String -> IO ())))
  , svStartWC    :: !(IORef UTCTime)
  , svLastStatWC :: !(IORef UTCTime)

  , svCheckModel :: !(IORef Bool)

  , svRandomFreq :: !(IORef Double)
  , svRandomGen  :: !(IORef Rand.StdGen)

  , svFailedAssumptions :: !(IORef [Lit])

  , svConfBudget :: !(IORef Int)
  }

markBad :: Solver -> IO ()
markBad solver = do
  writeIORef (svOk solver) False
  SQ.clear (svBCPQueue solver)

bcpEnqueue :: Solver -> Lit -> IO ()
bcpEnqueue solver l = SQ.enqueue (svBCPQueue solver) l

bcpDequeue :: Solver -> IO (Maybe Lit)
bcpDequeue solver = SQ.dequeue (svBCPQueue solver)

bcpCheckEmpty :: Solver -> IO ()
bcpCheckEmpty solver = do
  size <- SQ.queueSize (svBCPQueue solver)
  unless (size == 0) $
    error "BUG: BCP Queue should be empty at this point"

assignBy :: ConstraintHandler c => Solver -> Lit -> c -> IO Bool
assignBy solver lit c = do
  lv <- readIORef (svLevel solver)
  let !c2 = if lv == levelRoot
            then Nothing
            else Just $! toConstraintHandler c
  assign_ solver lit c2

assign :: Solver -> Lit -> IO Bool
assign solver lit = assign_ solver lit Nothing

assign_ :: Solver -> Lit -> Maybe SomeConstraintHandler -> IO Bool
assign_ solver !lit reason = assert (validLit lit) $ do
  vd <- varData solver (litVar lit)
  m <- readIORef (vdAssignment vd)
  case m of
    Just a -> return $ litPolarity lit == aValue a
    Nothing -> do
      idx <- readIORef (svNAssigns solver)
      lv <- readIORef (svLevel solver)
      bt <- newIORef []

      writeIORef (vdAssignment vd) $ Just $!
        Assignment
        { aValue  = litPolarity lit
        , aIndex  = idx
        , aLevel  = lv
        , aReason = reason
        , aBacktrackCBs = bt
        }

      modifyIORef (svTrail solver) (lit:)
      modifyIORef' (svNAssigns solver) (+1)
      when (lv == levelRoot) $ modifyIORef' (svNFixed solver) (+1)
      bcpEnqueue solver lit

      when debugMode $ logIO solver $ do
        let r = case reason of
                  Nothing -> ""
                  Just _ -> " by propagation"
        return $ printf "assign(level=%d): %d%s" lv lit r

      return True

unassign :: Solver -> Var -> IO ()
unassign solver !v = assert (validVar v) $ do
  vd <- varData solver v
  m <- readIORef (vdAssignment vd)
  case m of
    Nothing -> error "unassign: should not happen"
    Just a -> do
      flag <- getEnablePhaseSaving solver
      when flag $ writeIORef (vdPolarity vd) (aValue a)
      readIORef (aBacktrackCBs a) >>= sequence_
  writeIORef (vdAssignment vd) Nothing
  modifyIORef' (svNAssigns solver) (subtract 1)
  PQ.enqueue (svVarQueue solver) v

addBacktrackCB :: Solver -> Var -> IO () -> IO ()
addBacktrackCB solver !v callback = do
  vd <- varData solver v
  m <- readIORef (vdAssignment vd)
  case m of
    Nothing -> error "addBacktrackCB: should not happen"
    Just a -> modifyIORef (aBacktrackCBs a) (callback :)

-- | Register the constraint to be notified when the literal becames false.
watch :: ConstraintHandler c => Solver -> Lit -> c -> IO ()
watch solver !lit c = do
  when debugMode $ do
    lits <- watchedLiterals solver c
    unless (lit `elem` lits) $ error "watch: should not happen"
  ld <- litData solver lit
  modifyIORef (ldWatches ld) (toConstraintHandler c : )

-- | Register the constraint to be notified when the variable is assigned.
watchVar :: ConstraintHandler c => Solver -> Var -> c -> IO ()
watchVar solver !var c = do
  when debugMode $ do
    vs <- watchedVariables solver c
    unless (var `elem` vs) $ error "watchVar: should not happen"
  vd <- varData solver var
  modifyIORef (vdWatches vd) (toConstraintHandler c : )

-- | Returns list of constraints that are watching the literal.
watches :: Solver -> Lit -> IO [SomeConstraintHandler]
watches solver !lit = do
  ld <- litData solver lit
  readIORef (ldWatches ld)

addToDB :: ConstraintHandler c => Solver -> c -> IO ()
addToDB solver c = do
  let c2 = toConstraintHandler c
  modifyIORef (svConstrDB solver) (c2 : )
  when debugMode $ logIO solver $ do
    str <- showConstraintHandler solver c
    return $ printf "constraint %s is added" str

  b <- isPBRepresentable solver c
  when b $ do
    (lhs,_) <- toPBLinAtLeast solver c
    forM_ lhs $ \(_,lit) -> do
       ld <- litData solver lit
       modifyIORef' (ldOccurList ld) (HashSet.insert c2)

  sanityCheck solver

addToLearntDB :: ConstraintHandler c => Solver -> c -> IO ()
addToLearntDB solver c = do
  modifyIORef (svLearntDB solver) $ \(n,xs) -> (n+1, toConstraintHandler c : xs)
  when debugMode $ logIO solver $ do
    str <- showConstraintHandler solver c
    return $ printf "constraint %s is added" str
  sanityCheck solver

reduceDB :: Solver -> IO ()
reduceDB solver = do
  (_,cs) <- readIORef (svLearntDB solver)

  xs <- forM cs $ \c -> do
    p <- constrIsProtected solver c
    w <- constrWeight solver c
    actval <- constrReadActivity c
    return (c, (p, w*actval))

  -- Note that False <= True
  let ys = sortBy (comparing snd) xs
      (zs,ws) = splitAt (length ys `div` 2) ys

  let loop [] ret = return ret
      loop ((c,(isShort,_)) : rest) ret = do
        flag <- if isShort
                then return True
                else isLocked solver c
        if flag then
          loop rest (c:ret)
        else do
          detach solver c
          loop rest ret
  zs2 <- loop zs []

  let cs2 = zs2 ++ map fst ws
      n2 = length cs2

  -- log solver $ printf "learnt constraints deletion: %d -> %d" n n2
  writeIORef (svLearntDB solver) (n2,cs2)

type VarActivity = Double

varActivity :: Solver -> Var -> IO VarActivity
varActivity solver !v = do
  vd <- varData solver v
  readIORef (vdActivity vd)

varDecayActivity :: Solver -> IO ()
varDecayActivity solver = do
  d <- readIORef (svVarDecay solver)
  modifyIORef' (svVarInc solver) (d*)

varBumpActivity :: Solver -> Var -> IO ()
varBumpActivity solver !v = do
  inc <- readIORef (svVarInc solver)
  vd <- varData solver v
  modifyIORef' (vdActivity vd) (+inc)
  PQ.update (svVarQueue solver) v
  aval <- readIORef (vdActivity vd)
  when (aval > 1e20) $
    -- Rescale
    varRescaleAllActivity solver

varRescaleAllActivity :: Solver -> IO ()
varRescaleAllActivity solver = do
  vs <- variables solver
  forM_ vs $ \v -> do
    vd <- varData solver v
    modifyIORef' (vdActivity vd) (* 1e-20)
  modifyIORef' (svVarInc solver) (* 1e-20)

variables :: Solver -> IO [Var]
variables solver = do
  n <- nVars solver
  return [1 .. n]

-- | number of variables of the problem.
nVars :: Solver -> IO Int
nVars solver = Vec.getSize (svVarData solver)

-- | number of assigned variables.
nAssigns :: Solver -> IO Int
nAssigns solver = readIORef (svNAssigns solver)

-- | number of constraints.
nConstraints :: Solver -> IO Int
nConstraints solver = do
  xs <- readIORef (svConstrDB solver)
  return $ length xs

-- | number of learnt constrints.
nLearnt :: Solver -> IO Int
nLearnt solver = do
  (n,_) <- readIORef (svLearntDB solver)
  return n

learntConstraints :: Solver -> IO [SomeConstraintHandler]
learntConstraints solver = do
  (_,cs) <- readIORef (svLearntDB solver)
  return cs

{--------------------------------------------------------------------
  Solver
--------------------------------------------------------------------}

-- | Create a new Solver instance.
newSolver :: IO Solver
newSolver = do
 rec
  ok   <- newIORef True
  trail <- newIORef []
  vars <- Vec.new
  vqueue <- PQ.newPriorityQueueBy (ltVar solver)
  db  <- newIORef []
  db2 <- newIORef (0,[])
  as  <- newIORef =<< newArray_ (0,-1)
  lv  <- newIORef levelRoot
  q   <- SQ.newFifo
  m   <- newIORef Nothing
  ndecision <- newIORef 0
  nranddec  <- newIORef 0
  nconflict <- newIORef 0
  nrestart  <- newIORef 0
  nassigns  <- newIORef 0
  nfixed    <- newIORef 0
  nlearntgc <- newIORef 0
  nremoved  <- newIORef 0

  constrDecay <- newIORef (1 / 0.999)
  constrInc   <- newIORef 1
  varDecay <- newIORef (1 / 0.95)
  varInc   <- newIORef 1
  restartStrat <- newIORef defaultRestartStrategy
  restartFirst <- newIORef defaultRestartFirst
  restartInc <- newIORef defaultRestartInc
  learning <- newIORef defaultLearningStrategy
  learntSizeFirst <- newIORef defaultLearntSizeFirst
  learntSizeInc <- newIORef defaultLearntSizeInc
  ccMin <- newIORef defaultCCMin
  checkModel <- newIORef False
  pbHandlerType <- newIORef defaultPBHandlerType
  enablePhaseSaving <- newIORef defaultEnablePhaseSaving
  enableForwardSubsumptionRemoval <- newIORef defaultEnableForwardSubsumptionRemoval
  enableBackwardSubsumptionRemoval <- newIORef defaultEnableBackwardSubsumptionRemoval

  learntLim       <- newIORef undefined
  learntLimAdjCnt <- newIORef (-1)
  learntLimSeq    <- newIORef undefined

  logger <- newIORef Nothing
  startWC    <- newIORef undefined
  lastStatWC <- newIORef undefined

  randfreq <- newIORef defaultRandomFreq
  randgen  <- newIORef =<< Rand.newStdGen

  failed <- newIORef []

  confBudget <- newIORef (-1)

  let solver =
        Solver
        { svOk = ok
        , svVarQueue   = vqueue
        , svTrail      = trail
        , svVarData    = vars
        , svConstrDB   = db
        , svLearntDB   = db2
        , svAssumptions = as
        , svLevel      = lv
        , svBCPQueue   = q
        , svModel      = m
        , svNDecision  = ndecision
        , svNRandomDecision = nranddec
        , svNConflict  = nconflict
        , svNRestart   = nrestart
        , svNAssigns   = nassigns
        , svNFixed     = nfixed
        , svNLearntGC  = nlearntgc
        , svNRemovedConstr = nremoved
        , svVarDecay    = varDecay
        , svVarInc      = varInc
        , svConstrDecay = constrDecay
        , svConstrInc   = constrInc
        , svRestartStrategy = restartStrat
        , svRestartFirst = restartFirst
        , svRestartInc   = restartInc
        , svLearningStrategy = learning
        , svLearntSizeFirst = learntSizeFirst
        , svLearntSizeInc = learntSizeInc
        , svCCMin = ccMin
        , svEnablePhaseSaving = enablePhaseSaving
        , svEnableForwardSubsumptionRemoval = enableForwardSubsumptionRemoval
        , svPBHandlerType   = pbHandlerType
        , svEnableBackwardSubsumptionRemoval = enableBackwardSubsumptionRemoval
        , svLearntLim       = learntLim
        , svLearntLimAdjCnt = learntLimAdjCnt
        , svLearntLimSeq    = learntLimSeq
        , svLogger = logger
        , svStartWC    = startWC
        , svLastStatWC = lastStatWC
        , svCheckModel = checkModel
        , svRandomFreq = randfreq
        , svRandomGen  = randgen
        , svFailedAssumptions = failed
        , svConfBudget = confBudget
        }
 return solver

ltVar :: Solver -> Var -> Var -> IO Bool
ltVar solver v1 v2 = do
  a1 <- varActivity solver v1
  a2 <- varActivity solver v2
  return $! a1 > a2

{--------------------------------------------------------------------
  Problem specification
--------------------------------------------------------------------}

-- |Add a new variable
newVar :: Solver -> IO Var
newVar solver = do
  n <- Vec.getSize (svVarData solver)
  let v = n + 1
  vd <- newVarData
  Vec.push (svVarData solver) vd
  PQ.enqueue (svVarQueue solver) v
  return v

-- |Add variables. @newVars solver n = replicateM n (newVar solver)@
newVars :: Solver -> Int -> IO [Var]
newVars solver n = do
  nv <- nVars solver
  resizeVarCapacity solver (nv+n)
  replicateM n (newVar solver)

-- |Add variables. @newVars_ solver n = newVars solver n >> return ()@
newVars_ :: Solver -> Int -> IO ()
newVars_ solver n = do
  nv <- nVars solver
  resizeVarCapacity solver (nv+n)
  replicateM_ n (newVar solver)

-- |Pre-allocate internal buffer for @n@ variables.
resizeVarCapacity :: Solver -> Int -> IO ()
resizeVarCapacity solver n = do
  Vec.resizeCapacity (svVarData solver) n
  PQ.resizeHeapCapacity (svVarQueue solver) n
  PQ.resizeTableCapacity (svVarQueue solver) (n+1)

-- |Add a clause to the solver.
addClause :: Solver -> Clause -> IO ()
addClause solver lits = do
  d <- readIORef (svLevel solver)
  assert (d == levelRoot) $ return ()

  ok <- readIORef (svOk solver)
  when ok $ do
    lits2 <- instantiateClause solver lits
    case normalizeClause =<< lits2 of
      Nothing -> return ()
      Just [] -> markBad solver
      Just [lit] -> do
        {- We do not call 'removeBackwardSubsumedBy' here,
           because subsumed constraints will be removed by 'simplify'. -}
        ret <- assign solver lit
        assert ret $ return ()
        ret2 <- deduce solver
        case ret2 of
          Nothing -> return ()
          Just _ -> markBad solver
      Just lits3 -> do
        subsumed <- checkForwardSubsumption solver lits
        unless subsumed $ do
          removeBackwardSubsumedBy solver ([(1,lit) | lit <- lits3], 1)
          clause <- newClauseHandler lits3 False
          addToDB solver clause
          _ <- basicAttachClauseHandler solver clause
          return ()

-- | Add a cardinality constraints /atleast({l1,l2,..},n)/.
addAtLeast :: Solver -- ^ The 'Solver' argument.
           -> [Lit]  -- ^ set of literals /{l1,l2,..}/ (duplicated elements are ignored)
           -> Int    -- ^ /n/.
           -> IO ()
addAtLeast solver lits n = do
  d <- readIORef (svLevel solver)
  assert (d == levelRoot) $ return ()

  ok <- readIORef (svOk solver)
  when ok $ do
    (lits',n') <- liftM normalizeAtLeast $ instantiateAtLeast solver (lits,n)
    let len = length lits'

    if n' <= 0 then return ()
    else if n' > len then markBad solver
    else if n' == 1 then addClause solver lits'
    else if n' == len then do
      {- We do not call 'removeBackwardSubsumedBy' here,
         because subsumed constraints will be removed by 'simplify'. -}
      forM_ lits' $ \l -> do
        ret <- assign solver l
        assert ret $ return ()
      ret2 <- deduce solver
      case ret2 of
        Nothing -> return ()
        Just _ -> markBad solver
    else do
      removeBackwardSubsumedBy solver ([(1,lit) | lit <- lits'], fromIntegral n')
      c <- newAtLeastHandler lits' n' False
      addToDB solver c
      _ <- basicAttachAtLeastHandler solver c
      return ()

-- | Add a cardinality constraints /atmost({l1,l2,..},n)/.
addAtMost :: Solver -- ^ The 'Solver' argument
          -> [Lit]  -- ^ set of literals /{l1,l2,..}/ (duplicated elements are ignored)
          -> Int    -- ^ /n/
          -> IO ()
addAtMost solver lits n = addAtLeast solver lits' (len-n)
  where
    len   = length lits
    lits' = map litNot lits

-- | Add a cardinality constraints /exactly({l1,l2,..},n)/.
addExactly :: Solver -- ^ The 'Solver' argument
           -> [Lit]  -- ^ set of literals /{l1,l2,..}/ (duplicated elements are ignored)
           -> Int    -- ^ /n/
           -> IO ()
addExactly solver lits n = do
  addAtLeast solver lits n
  addAtMost solver lits n

-- | Add a pseudo boolean constraints /c1*l1 + c2*l2 + … ≥ n/.
addPBAtLeast :: Solver          -- ^ The 'Solver' argument.
             -> [(Integer,Lit)] -- ^ set of terms @[(c1,l1),(c2,l2),…]@
             -> Integer         -- ^ /n/
             -> IO ()
addPBAtLeast solver ts n = do
  d <- readIORef (svLevel solver)
  assert (d == levelRoot) $ return ()

  ok <- readIORef (svOk solver)
  when ok $ do
    (ts',degree) <- liftM normalizePBLinAtLeast $ instantiatePB solver (ts,n)
  
    case pbToAtLeast (ts',degree) of
      Just (lhs',rhs') -> addAtLeast solver lhs' rhs'
      Nothing -> do
        let cs = map fst ts'
            slack = sum cs - degree
        if degree <= 0 then return ()
        else if slack < 0 then markBad solver
        else do
          removeBackwardSubsumedBy solver (ts', degree)
          c <- newPBHandler solver ts' degree False
          addToDB solver c
          ret <- attach solver c
          if not ret then do
            markBad solver
          else do
            ret2 <- deduce solver
            case ret2 of
              Nothing -> return ()
              Just _ -> markBad solver

-- | Add a pseudo boolean constraints /c1*l1 + c2*l2 + … ≤ n/.
addPBAtMost :: Solver          -- ^ The 'Solver' argument.
            -> [(Integer,Lit)] -- ^ list of @[(c1,l1),(c2,l2),…]@
            -> Integer         -- ^ /n/
            -> IO ()
addPBAtMost solver ts n = addPBAtLeast solver [(-c,l) | (c,l) <- ts] (negate n)

-- | Add a pseudo boolean constraints /c1*l1 + c2*l2 + … = n/.
addPBExactly :: Solver          -- ^ The 'Solver' argument.
             -> [(Integer,Lit)] -- ^ list of terms @[(c1,l1),(c2,l2),…]@
             -> Integer         -- ^ /n/
             -> IO ()
addPBExactly solver ts n = do
  (ts2,n2) <- liftM normalizePBLinExactly $ instantiatePB solver (ts,n)
  addPBAtLeast solver ts2 n2
  addPBAtMost solver ts2 n2

-- | Add a soft pseudo boolean constraints /lit ⇒ c1*l1 + c2*l2 + … ≥ n/.
addPBAtLeastSoft
  :: Solver          -- ^ The 'Solver' argument.
  -> Lit             -- ^ indicator @lit@
  -> [(Integer,Lit)] -- ^ set of terms @[(c1,l1),(c2,l2),…]@
  -> Integer         -- ^ /n/
  -> IO ()
addPBAtLeastSoft solver sel lhs rhs = do
  (lhs', rhs') <- liftM normalizePBLinAtLeast $ instantiatePB solver (lhs,rhs)
  addPBAtLeast solver ((rhs', litNot sel) : lhs') rhs'

-- | Add a soft pseudo boolean constraints /lit ⇒ c1*l1 + c2*l2 + … ≤ n/.
addPBAtMostSoft
  :: Solver          -- ^ The 'Solver' argument.
  -> Lit             -- ^ indicator @lit@
  -> [(Integer,Lit)] -- ^ set of terms @[(c1,l1),(c2,l2),…]@
  -> Integer         -- ^ /n/
  -> IO ()
addPBAtMostSoft solver sel lhs rhs =
  addPBAtLeastSoft solver sel [(negate c, lit) | (c,lit) <- lhs] (negate rhs)

-- | Add a soft pseudo boolean constraints /lit ⇒ c1*l1 + c2*l2 + … = n/.
addPBExactlySoft
  :: Solver          -- ^ The 'Solver' argument.
  -> Lit             -- ^ indicator @lit@
  -> [(Integer,Lit)] -- ^ set of terms @[(c1,l1),(c2,l2),…]@
  -> Integer         -- ^ /n/
  -> IO ()
addPBExactlySoft solver sel lhs rhs = do
  (lhs2, rhs2) <- liftM normalizePBLinExactly $ instantiatePB solver (lhs,rhs)
  addPBAtLeastSoft solver sel lhs2 rhs2
  addPBAtMostSoft solver sel lhs2 rhs2

{--------------------------------------------------------------------
  Problem solving
--------------------------------------------------------------------}

-- | Solve constraints.
-- Returns 'True' if the problem is SATISFIABLE.
-- Returns 'False' if the problem is UNSATISFIABLE.
solve :: Solver -> IO Bool
solve solver = do
  as <- newArray_ (0,-1)
  writeIORef (svAssumptions solver) as
  solve_ solver

-- | Solve constraints under assuptions.
-- Returns 'True' if the problem is SATISFIABLE.
-- Returns 'False' if the problem is UNSATISFIABLE.
solveWith :: Solver
          -> [Lit]    -- ^ Assumptions
          -> IO Bool
solveWith solver ls = do
  as <- newListArray (0, length ls -1) ls
  writeIORef (svAssumptions solver) as
  solve_ solver

solve_ :: Solver -> IO Bool
solve_ solver = do
  log solver "Solving starts ..."
  resetStat solver
  writeIORef (svModel solver) Nothing
  writeIORef (svFailedAssumptions solver) []

  ok <- readIORef (svOk solver)
  if not ok then
    return False
  else do
    when debugMode $ dumpVarActivity solver
    d <- readIORef (svLevel solver)
    assert (d == levelRoot) $ return ()

    restartStrategy <- readIORef (svRestartStrategy solver)
    restartFirst  <- readIORef (svRestartFirst solver)
    restartInc    <- readIORef (svRestartInc solver)
    let restartSeq = mkRestartSeq restartStrategy restartFirst restartInc

    let learntSizeAdj = do
          (size,adj) <- shift (svLearntLimSeq solver)
          writeIORef (svLearntLim solver) size
          writeIORef (svLearntLimAdjCnt solver) adj
        onConflict = do
          cnt <- readIORef (svLearntLimAdjCnt solver)
          if (cnt==0)
          then learntSizeAdj
          else writeIORef (svLearntLimAdjCnt solver) $! cnt-1

    cnt <- readIORef (svLearntLimAdjCnt solver)
    when (cnt == -1) $ do
      learntSizeFirst <- readIORef (svLearntSizeFirst solver)
      learntSizeInc   <- readIORef (svLearntSizeInc solver)
      nc <- nConstraints solver
      nv <- nVars solver
      let initialLearntLim = if learntSizeFirst > 0 then learntSizeFirst else max ((nc + nv) `div` 3) 16
          learntSizeSeq    = iterate (ceiling . (learntSizeInc*) . fromIntegral) initialLearntLim
          learntSizeAdjSeq = iterate (\x -> (x * 3) `div` 2) (100::Int)
      writeIORef (svLearntLimSeq solver) (zip learntSizeSeq learntSizeAdjSeq)
      learntSizeAdj

    let loop [] = error "solve_: should not happen"
        loop (conflict_lim:rs) = do
          printStat solver True
          ret <- search solver conflict_lim onConflict
          case ret of
            SRFinished x -> return $ Just x
            SRBudgetExceeded -> return Nothing
            SRRestart -> do
              modifyIORef' (svNRestart solver) (+1)
              backtrackTo solver levelRoot
              loop rs

    printStatHeader solver

    startCPU <- getCPUTime
    startWC  <- getCurrentTime
    writeIORef (svStartWC solver) startWC
    result <- loop restartSeq
    endCPU <- getCPUTime
    endWC  <- getCurrentTime

    when (result == Just True) $ do
      checkModel <- readIORef (svCheckModel solver)
      when checkModel $ checkSatisfied solver
      constructModel solver

    backtrackTo solver levelRoot

    when debugMode $ dumpVarActivity solver
    when debugMode $ dumpConstrActivity solver
    printStat solver True
    (log solver . printf "#cpu_time = %.3fs") (fromIntegral (endCPU - startCPU) / 10^(12::Int) :: Double)
    (log solver . printf "#wall_clock_time = %.3fs") (realToFrac (endWC `diffUTCTime` startWC) :: Double)
    (log solver . printf "#decision = %d") =<< readIORef (svNDecision solver)
    (log solver . printf "#random_decision = %d") =<< readIORef (svNRandomDecision solver)
    (log solver . printf "#conflict = %d") =<< readIORef (svNConflict solver)
    (log solver . printf "#restart = %d")  =<< readIORef (svNRestart solver)

    case result of
      Just x  -> return x
      Nothing -> throw BudgetExceeded

data BudgetExceeded = BudgetExceeded
  deriving (Show, Typeable)

instance Exception BudgetExceeded

data SearchResult
  = SRFinished Bool
  | SRRestart
  | SRBudgetExceeded

search :: Solver -> Int -> IO () -> IO SearchResult
search solver !conflict_lim onConflict = do
  conflictCounter <- newIORef 0
  let 
    loop :: IO SearchResult
    loop = do
      sanityCheck solver
      conflict <- deduce solver
      sanityCheck solver
      case conflict of
        Just constr -> do
          ret <- handleConflict conflictCounter constr
          case ret of
            Just sr -> return sr
            Nothing -> loop
        Nothing -> do
          lv <- readIORef (svLevel solver)
          when (lv == levelRoot) $ simplify solver
          checkGC
          r <- pickAssumption
          case r of
            Nothing -> return (SRFinished False)
            Just lit
              | lit /= litUndef -> decide solver lit >> loop
              | otherwise -> do
                  lit2 <- pickBranchLit solver
                  if lit2 == litUndef
                    then return (SRFinished True)
                    else decide solver lit2 >> loop
  loop

  where
    checkGC :: IO ()
    checkGC = do
      n <- nLearnt solver
      m <- nAssigns solver
      learnt_lim <- readIORef (svLearntLim solver)
      when (learnt_lim >= 0 && n - m > learnt_lim) $ do
        modifyIORef' (svNLearntGC solver) (+1)
        reduceDB solver

    pickAssumption :: IO (Maybe Lit)
    pickAssumption = do
      !as <- readIORef (svAssumptions solver)
      !b <- getBounds as
      let go = do
              d <- readIORef (svLevel solver)
              if not (inRange b (d+1)) then
                return (Just litUndef)
              else do
                l <- readArray as (d+1)
                val <- litValue solver l
                if val == lTrue then do
                  -- dummy decision level
                  modifyIORef' (svLevel solver) (+1)
                  go
                else if val == lFalse then do
                  -- conflict with assumption
                  core <- analyzeFinal solver l
                  writeIORef (svFailedAssumptions solver) core
                  return Nothing
                else
                  return (Just l)
      go

    handleConflict :: IORef Int -> SomeConstraintHandler -> IO (Maybe SearchResult)
    handleConflict conflictCounter constr = do
      varDecayActivity solver
      constrDecayActivity solver
      onConflict

      modifyIORef' (svNConflict solver) (+1)
      d <- readIORef (svLevel solver)

      when debugMode $ logIO solver $ do
        str <- showConstraintHandler solver constr
        return $ printf "conflict(level=%d): %s" d str

      modifyIORef' conflictCounter (+1)
      c <- readIORef conflictCounter

      modifyIORef' (svConfBudget solver) $ \confBudget ->
        if confBudget > 0 then confBudget - 1 else confBudget
      confBudget <- readIORef (svConfBudget solver)

      when (c `mod` 100 == 0) $ do
        printStat solver False

      if d == levelRoot then do
        markBad solver
        return $ Just (SRFinished False)
      else if confBudget==0 then
        return $ Just SRBudgetExceeded
      else if conflict_lim >= 0 && c >= conflict_lim then
        return $ Just SRRestart
      else do
        strat <- readIORef (svLearningStrategy solver)
        case strat of
          LearningClause -> learnClause constr >> return Nothing
          LearningHybrid -> learnHybrid conflictCounter constr

    learnClause :: SomeConstraintHandler -> IO ()
    learnClause constr = do
      (learntClause, level) <- analyzeConflict solver constr
      backtrackTo solver level
      case learntClause of
        [] -> error "search(LearningClause): should not happen"
        [lit] -> do
          ret <- assign solver lit
          assert ret $ return ()
          return ()
        lit:_ -> do
          cl <- newClauseHandler learntClause True
          addToLearntDB solver cl
          basicAttachClauseHandler solver cl
          assignBy solver lit cl
          constrBumpActivity solver cl

    learnHybrid :: IORef Int -> SomeConstraintHandler -> IO (Maybe SearchResult)
    learnHybrid conflictCounter constr = do
      ((learntClause, clauseLevel), (pb, pbLevel)) <- analyzeConflictHybrid solver constr
      let minLevel = min clauseLevel pbLevel
      backtrackTo solver minLevel

      case learntClause of
        [] -> error "search(LearningHybrid): should not happen"
        [lit] -> do
          _ <- assign solver lit -- This should always succeed.
          return ()
        lit:_ -> do
          cl <- newClauseHandler learntClause True
          addToLearntDB solver cl
          basicAttachClauseHandler solver cl
          constrBumpActivity solver cl
          when (minLevel == clauseLevel) $ do
            _ <- assignBy solver lit cl -- This should always succeed.
            return ()

      ret <- deduce solver
      case ret of
        Just conflicted -> do
          handleConflict conflictCounter conflicted
          -- TODO: should also learn the PB constraint?
        Nothing -> do
          let (lhs,rhs) = pb
          h <- newPBHandlerPromoted solver lhs rhs True
          case h of
            CHClause _ -> do
              {- We don't want to add additional clause,
                 since it would be subsumed by already added one. -}
              return Nothing
            _ -> do
              addToLearntDB solver h
              ret2 <- attach solver h
              constrBumpActivity solver h
              if ret2 then
                return Nothing
              else
                handleConflict conflictCounter h

-- | After 'solve' returns True, it returns the model.
model :: Solver -> IO Model
model solver = do
  m <- readIORef (svModel solver)
  return (fromJust m)

-- | After 'solveWith' returns False, it returns a set of assumptions
-- that leads to contradiction. In particular, if it returns an empty
-- set, the problem is unsatisiable without any assumptions.
failedAssumptions :: Solver -> IO [Lit]
failedAssumptions solver = readIORef (svFailedAssumptions solver)

{--------------------------------------------------------------------
  Simplification
--------------------------------------------------------------------}

-- | Simplify the constraint database according to the current top-level assigment.
simplify :: Solver -> IO ()
simplify solver = do
  let loop [] rs !n     = return (rs,n)
      loop (y:ys) rs !n = do
        b1 <- isSatisfied solver y
        b2 <- isLocked solver y
        if b1 && not b2 then do
          detach solver y
          loop ys rs (n+1)
        else loop ys (y:rs) n

  -- simplify original constraint DB
  do
    xs <- readIORef (svConstrDB solver)
    (ys,n) <- loop xs [] (0::Int)
    modifyIORef' (svNRemovedConstr solver) (+n)
    writeIORef (svConstrDB solver) ys

  -- simplify learnt constraint DB
  do
    (m,xs) <- readIORef (svLearntDB solver)
    (ys,n) <- loop xs [] (0::Int)
    writeIORef (svLearntDB solver) (m-n, ys)

{-
References:
L. Zhang, "On subsumption removal and On-the-Fly CNF simplification,"
Theory and Applications of Satisfiability Testing (2005), pp. 482-489.
-}

checkForwardSubsumption :: Solver -> Clause -> IO Bool
checkForwardSubsumption solver lits = do
  flag <- getEnableForwardSubsumptionRemoval solver
  if not flag then
    return False
  else do
    withEnablePhaseSaving solver False $ do
      bracket_
        (modifyIORef' (svLevel solver) (+1))
        (backtrackTo solver levelRoot) $ do
          b <- allM (\lit -> assign solver (litNot lit)) lits
          if b then
            liftM isJust (deduce solver)
          else do
            when debugMode $ log solver ("forward subsumption: " ++ show lits)
            return True
  where
    withEnablePhaseSaving solver flag m =
      bracket
        (getEnablePhaseSaving solver)
        (setEnablePhaseSaving solver)
        (\_ -> setEnablePhaseSaving solver flag >> m)

removeBackwardSubsumedBy :: Solver -> PBLinAtLeast -> IO ()
removeBackwardSubsumedBy solver pb = do
  flag <- getEnableBackwardSubsumptionRemoval solver
  when flag $ do
    xs <- backwardSubsumedBy solver pb
    when debugMode $ do
      forM_ (HashSet.toList xs) $ \c -> do
        s <- showConstraintHandler solver c
        log solver (printf "backward subsumption: %s is subsumed by %s\n" s (show pb))
    removeConstraintHandlers solver xs

backwardSubsumedBy :: Solver -> PBLinAtLeast -> IO (HashSet SomeConstraintHandler)
backwardSubsumedBy solver pb@(lhs,_) = do
  xs <- forM lhs $ \(_,lit) -> do
    ld <- litData solver lit
    readIORef (ldOccurList ld)
  case xs of
    [] -> return HashSet.empty
    s:ss -> do
      let p c = do
            -- Note that @isPBRepresentable c@ is always True here,
            -- because only such constraints are added to occur list.
            -- See 'addToDB'.
            pb2 <- instantiatePB solver =<< toPBLinAtLeast solver c
            return $ pbSubsume pb pb2
      liftM HashSet.fromList
        $ filterM p
        $ HashSet.toList
        $ foldl' HashSet.intersection s ss

removeConstraintHandlers :: Solver -> HashSet SomeConstraintHandler -> IO ()
removeConstraintHandlers _ zs | HashSet.null zs = return ()
removeConstraintHandlers solver zs = do
  let loop [] rs !n     = return (rs,n)
      loop (c:cs) rs !n = do
        if c `HashSet.member` zs then do
          detach solver c
          loop cs rs (n+1)
        else loop cs (c:rs) n
  xs <- readIORef (svConstrDB solver)
  (ys,n) <- loop xs [] (0::Int)
  modifyIORef' (svNRemovedConstr solver) (+n)
  writeIORef (svConstrDB solver) ys

{--------------------------------------------------------------------
  Parameter settings.
--------------------------------------------------------------------}

setRestartStrategy :: Solver -> RestartStrategy -> IO ()
setRestartStrategy solver s = writeIORef (svRestartStrategy solver) s

-- | default value for @RestartStrategy@.
defaultRestartStrategy :: RestartStrategy
defaultRestartStrategy = MiniSATRestarts

-- | The initial restart limit. (default 100)
-- Negative value is used to disable restart.
setRestartFirst :: Solver -> Int -> IO ()
setRestartFirst solver !n = writeIORef (svRestartFirst solver) n

-- | default value for @RestartFirst@.
defaultRestartFirst :: Int
defaultRestartFirst = 100

-- | The factor with which the restart limit is multiplied in each restart. (default 1.5)
setRestartInc :: Solver -> Double -> IO ()
setRestartInc solver !r = writeIORef (svRestartInc solver) r

-- | default value for @RestartInc@.
defaultRestartInc :: Double
defaultRestartInc = 1.5

data LearningStrategy
  = LearningClause
  | LearningHybrid

setLearningStrategy :: Solver -> LearningStrategy -> IO ()
setLearningStrategy solver l = writeIORef (svLearningStrategy solver) $! l

defaultLearningStrategy :: LearningStrategy
defaultLearningStrategy = LearningClause

-- | The initial limit for learnt clauses.
setLearntSizeFirst :: Solver -> Int -> IO ()
setLearntSizeFirst solver !x = writeIORef (svLearntSizeFirst solver) x

-- | default value for @LearntSizeFirst@.
defaultLearntSizeFirst :: Int
defaultLearntSizeFirst = -1

-- | The limit for learnt clauses is multiplied with this factor each restart. (default 1.1)
setLearntSizeInc :: Solver -> Double -> IO ()
setLearntSizeInc solver !r = writeIORef (svLearntSizeInc solver) r

-- | default value for @LearntSizeInc@.
defaultLearntSizeInc :: Double
defaultLearntSizeInc = 1.1

-- | The limit for learnt clauses is multiplied with this factor each restart. (default 1.1)
setCCMin :: Solver -> Int -> IO ()
setCCMin solver !v = writeIORef (svCCMin solver) v

-- | default value for @CCMin@.
defaultCCMin :: Int
defaultCCMin = 2

-- | The default polarity of a variable.
setVarPolarity :: Solver -> Var -> Bool -> IO ()
setVarPolarity solver v val = do
  vd <- varData solver v
  writeIORef (vdPolarity vd) val

setCheckModel :: Solver -> Bool -> IO ()
setCheckModel solver flag = do
  writeIORef (svCheckModel solver) flag

-- | The frequency with which the decision heuristic tries to choose a random variable
setRandomFreq :: Solver -> Double -> IO ()
setRandomFreq solver r = do
  writeIORef (svRandomFreq solver) r

defaultRandomFreq :: Double
defaultRandomFreq = 0.005

-- | Set random generator used by the random variable selection
setRandomGen :: Solver -> Rand.StdGen -> IO ()
setRandomGen solver = writeIORef (svRandomGen solver)

-- | Get random generator used by the random variable selection
getRandomGen :: Solver -> IO Rand.StdGen
getRandomGen solver = readIORef (svRandomGen solver)

setConfBudget :: Solver -> Maybe Int -> IO ()
setConfBudget solver (Just b) | b >= 0 = writeIORef (svConfBudget solver) b
setConfBudget solver _ = writeIORef (svConfBudget solver) (-1)

data PBHandlerType = PBHandlerTypeCounter | PBHandlerTypePueblo
  deriving (Show, Eq, Ord)

defaultPBHandlerType :: PBHandlerType
defaultPBHandlerType = PBHandlerTypeCounter

setPBHandlerType :: Solver -> PBHandlerType -> IO ()
setPBHandlerType solver ht = do
  writeIORef (svPBHandlerType solver) ht

setEnablePhaseSaving :: Solver -> Bool -> IO ()
setEnablePhaseSaving solver flag = do
  writeIORef (svEnablePhaseSaving solver) flag

getEnablePhaseSaving :: Solver -> IO Bool
getEnablePhaseSaving solver = do
  readIORef (svEnablePhaseSaving solver)

defaultEnablePhaseSaving :: Bool
defaultEnablePhaseSaving = True

setEnableForwardSubsumptionRemoval :: Solver -> Bool -> IO ()
setEnableForwardSubsumptionRemoval solver flag = do
  writeIORef (svEnableForwardSubsumptionRemoval solver) flag

getEnableForwardSubsumptionRemoval :: Solver -> IO Bool
getEnableForwardSubsumptionRemoval solver = do
  readIORef (svEnableForwardSubsumptionRemoval solver)

defaultEnableForwardSubsumptionRemoval :: Bool
defaultEnableForwardSubsumptionRemoval = False

setEnableBackwardSubsumptionRemoval :: Solver -> Bool -> IO ()
setEnableBackwardSubsumptionRemoval solver flag = do
  writeIORef (svEnableBackwardSubsumptionRemoval solver) flag

getEnableBackwardSubsumptionRemoval :: Solver -> IO Bool
getEnableBackwardSubsumptionRemoval solver = do
  readIORef (svEnableBackwardSubsumptionRemoval solver)

defaultEnableBackwardSubsumptionRemoval :: Bool
defaultEnableBackwardSubsumptionRemoval = False

{--------------------------------------------------------------------
  API for implementation of @solve@
--------------------------------------------------------------------}

pickBranchLit :: Solver -> IO Lit
pickBranchLit !solver = do
  let vqueue = svVarQueue solver

  -- Random decision
  let withRandGen :: (Rand.StdGen -> (a, Rand.StdGen)) -> IO a
      withRandGen f = do
        randgen  <- readIORef (svRandomGen solver)
        let (r, randgen') = f randgen
        writeIORef (svRandomGen solver) randgen'
        return r
  !randfreq <- readIORef (svRandomFreq solver)
  !size <- PQ.queueSize vqueue
  !r <- withRandGen Rand.random
  var <-
    if (r < randfreq && size >= 2) then do
      a <- PQ.getHeapArray vqueue
      i <- withRandGen $ Rand.randomR (0, size-1)
      var <- readArray a i
      val <- varValue solver var
      if val == lUndef then do
        modifyIORef' (svNRandomDecision solver) (1+)
        return var
      else return litUndef
    else
      return litUndef

  -- Activity based decision
  let loop :: IO Var
      loop = do
        m <- PQ.dequeue vqueue
        case m of
          Nothing -> return litUndef
          Just var2 -> do
            val2 <- varValue solver var2
            if val2 /= lUndef
              then loop
              else return var2
  var2 <-
    if var==litUndef
    then loop
    else return var

  if var2==litUndef then
    return litUndef
  else do
    vd <- varData solver var2
    -- TODO: random polarity
    p <- readIORef (vdPolarity vd)
    return $! literal var2 p

decide :: Solver -> Lit -> IO ()
decide solver !lit = do
  modifyIORef' (svNDecision solver) (+1)
  modifyIORef' (svLevel solver) (+1)
  when debugMode $ do
    val <- litValue solver lit
    when (val /= lUndef) $ error "decide: should not happen"
  assign solver lit
  return ()

deduce :: Solver -> IO (Maybe SomeConstraintHandler)
deduce solver = loop
  where
    loop :: IO (Maybe SomeConstraintHandler)
    loop = do
      r <- bcpDequeue solver
      case r of
        Nothing -> return Nothing
        Just lit -> do
          ret <- processLit lit
          case ret of
            Just _ -> return ret
            Nothing -> do
              ret <- processVar (litVar lit)
              case ret of
                Just _ -> return ret
                Nothing -> loop

    processLit :: Lit -> IO (Maybe SomeConstraintHandler)
    processLit !lit = do
      let falsifiedLit = litNot lit
      ld <- litData solver falsifiedLit
      let wsref = ldWatches ld
      let loop2 [] = return Nothing
          loop2 (w:ws) = do
            ok <- propagate solver w falsifiedLit
            if ok then
              loop2 ws
            else do
              modifyIORef wsref (++ws)
              return (Just w)
      ws <- readIORef wsref
      writeIORef wsref []
      loop2 ws

    processVar :: Lit -> IO (Maybe SomeConstraintHandler)
    processVar !lit = do
      let falsifiedLit = litNot lit
      vd <- varData solver (litVar lit)
      let wsref = vdWatches vd
      let loop2 [] = return Nothing
          loop2 (w:ws) = do
            ok <- propagate solver w falsifiedLit
            if ok
              then loop2 ws
              else do
                modifyIORef wsref (++ws)
                return (Just w)
      ws <- readIORef wsref
      writeIORef wsref []
      loop2 ws

analyzeConflict :: ConstraintHandler c => Solver -> c -> IO (Clause, Level)
analyzeConflict solver constr = do
  d <- readIORef (svLevel solver)

  let split :: [Lit] -> IO (LitSet, LitSet)
      split = go (IS.empty, IS.empty)
        where
          go (xs,ys) [] = return (xs,ys)
          go (xs,ys) (l:ls) = do
            lv <- litLevel solver l
            if lv == levelRoot then
              go (xs,ys) ls
            else if lv >= d then
              go (IS.insert l xs, ys) ls
            else
              go (xs, IS.insert l ys) ls

  let loop :: LitSet -> LitSet -> IO LitSet
      loop lits1 lits2
        | sz==1 = do
            return $ lits1 `IS.union` lits2
        | sz>=2 = do
            l <- popTrail solver
            if litNot l `IS.notMember` lits1 then do
              unassign solver (litVar l)
              loop lits1 lits2
            else do
              m <- varReason solver (litVar l)
              case m of
                Nothing -> error "analyzeConflict: should not happen"
                Just constr2 -> do
                  constrBumpActivity solver constr2
                  xs <- reasonOf solver constr2 (Just l)
                  forM_ xs $ \lit -> varBumpActivity solver (litVar lit)
                  unassign solver (litVar l)
                  (ys,zs) <- split xs
                  loop (IS.delete (litNot l) lits1 `IS.union` ys)
                       (lits2 `IS.union` zs)
        | otherwise = error "analyzeConflict: should not happen: reason of current level is empty"
        where
          sz = IS.size lits1

  constrBumpActivity solver constr
  conflictClause <- reasonOf solver constr Nothing
  forM_ conflictClause $ \lit -> varBumpActivity solver (litVar lit)
  (ys,zs) <- split conflictClause
  lits <- loop ys zs

  lits2 <- minimizeConflictClause solver lits

  xs <- liftM (sortBy (flip (comparing snd))) $
    forM (IS.toList lits2) $ \l -> do
      lv <- litLevel solver l
      return (l,lv)

  let level = case xs of
                [] -> error "analyzeConflict: should not happen"
                [_] -> levelRoot
                _:(_,lv):_ -> lv
  return (map fst xs, level)

-- { p } ∪ { pにfalseを割り当てる原因のassumption }
analyzeFinal :: Solver -> Lit -> IO [Lit]
analyzeFinal solver p = do
  lits <- readIORef (svTrail solver)
  let go :: [Lit] -> VarSet -> [Lit] -> IO [Lit]
      go [] _ result = return result
      go (l:ls) seen result = do
        lv <- litLevel solver l
        if lv == levelRoot then
          return result
        else if litVar l `IS.member` seen then do
          r <- varReason solver (litVar l)
          case r of
            Nothing -> do
              let seen' = IS.delete (litVar l) seen
              go ls seen' (l : result)
            Just constr  -> do
              c <- reasonOf solver constr (Just l)
              let seen' = IS.delete (litVar l) seen `IS.union` IS.fromList [litVar l2 | l2 <- c]
              go ls seen' result
        else
          go ls seen result
  go lits (IS.singleton (litVar p)) [p]

analyzeConflictHybrid :: ConstraintHandler c => Solver -> c -> IO ((Clause, Level), (PBLinAtLeast, Level))
analyzeConflictHybrid solver constr = do
  d <- readIORef (svLevel solver)

  let split :: [Lit] -> IO (LitSet, LitSet)
      split = go (IS.empty, IS.empty)
        where
          go (xs,ys) [] = return (xs,ys)
          go (xs,ys) (l:ls) = do
            lv <- litLevel solver l
            if lv == levelRoot then
              go (xs,ys) ls
            else if lv >= d then
              go (IS.insert l xs, ys) ls
            else
              go (xs, IS.insert l ys) ls

  let loop :: LitSet -> LitSet -> PBLinAtLeast -> IO (LitSet, PBLinAtLeast)
      loop lits1 lits2 pb
        | sz==1 = do
            return $ (lits1 `IS.union` lits2, pb)
        | sz>=2 = do
            l <- popTrail solver
            m <- varReason solver (litVar l)
            case m of
              Nothing -> error "analyzeConflictHybrid: should not happen"
              Just constr2 -> do
                xs <- reasonOf solver constr2 (Just l)
                (lits1',lits2') <-
                  if litNot l `IS.notMember` lits1 then
                    return (lits1,lits2)
                  else do
                    constrBumpActivity solver constr2
                    forM_ xs $ \lit -> varBumpActivity solver (litVar lit)
                    (ys,zs) <- split xs
                    return  (IS.delete (litNot l) lits1 `IS.union` ys, lits2 `IS.union` zs)

                pb' <- if any (\(_,l2) -> litNot l == l2) (fst pb)
                       then do
                         pb2 <- do
                           b <- isPBRepresentable solver constr2
                           if not b then do
                             return $ clauseToPBLinAtLeast (l:xs)
                           else do
                             pb2 <- toPBLinAtLeast solver constr2
                             o <- pbOverSAT solver pb2
                             if o then
                               return $ clauseToPBLinAtLeast (l:xs)
                             else
                               return pb2
                         return $ cutResolve pb pb2 (litVar l)
                       else return pb

                unassign solver (litVar l)
                loop lits1' lits2' pb'

        | otherwise = error "analyzeConflictHybrid: should not happen: reason of current level is empty"
        where
          sz = IS.size lits1

  constrBumpActivity solver constr
  conflictClause <- reasonOf solver constr Nothing
  pbConfl <- do
    b <- isPBRepresentable solver constr
    if b then
      toPBLinAtLeast solver constr
    else
      return (clauseToPBLinAtLeast conflictClause)
  forM_ conflictClause $ \lit -> varBumpActivity solver (litVar lit)
  (ys,zs) <- split conflictClause
  (lits, pb) <- loop ys zs pbConfl

  lits2 <- minimizeConflictClause solver lits

  xs <- liftM (sortBy (flip (comparing snd))) $
    forM (IS.toList lits2) $ \l -> do
      lv <- litLevel solver l
      return (l,lv)

  let level = case xs of
                [] -> error "analyzeConflict: should not happen"
                [_] -> levelRoot
                _:(_,lv):_ -> lv
  pblevel <- pbBacktrackLevel solver pb
  return ((map fst xs, level), (pb, pblevel))

pbBacktrackLevel :: Solver -> PBLinAtLeast -> IO Level
pbBacktrackLevel _ ([], rhs) = assert (rhs > 0) $ return levelRoot
pbBacktrackLevel solver (lhs, rhs) = do
  levelToLiterals <- liftM (IM.unionsWith IM.union) $ forM lhs $ \(_,lit) -> do
    val <- litValue solver lit
    if val /= lUndef then do
      level <- litLevel solver lit
      return $ IM.singleton level (IM.singleton lit val)
    else
      return $ IM.empty

  let replay [] _ _ = error "pbBacktrackLevel: should not happen"
      replay ((lv,lv_lits) : lvs) lhs slack = do
        let slack_lv = slack - sum [c | (c,lit) <- lhs, IM.lookup lit lv_lits == Just lFalse]
            lhs_lv   = [tm | tm@(_,lit) <- lhs, IM.notMember lit lv_lits]
        if slack_lv < 0 then
          return lv -- CONFLICT
        else if any (\(c,_) -> c > slack_lv) lhs_lv then
          return lv -- UNIT
        else
          replay lvs lhs_lv slack_lv

  let initial_slack = sum [c | (c,_) <- lhs] - rhs
  replay (IM.toList levelToLiterals) lhs initial_slack

minimizeConflictClause :: Solver -> LitSet -> IO LitSet
minimizeConflictClause solver lits = do
  ccmin <- readIORef (svCCMin solver)
  if ccmin >= 2 then
    minimizeConflictClauseRecursive solver lits
  else if ccmin >= 1 then
    minimizeConflictClauseLocal solver lits
  else
    return lits

minimizeConflictClauseLocal :: Solver -> LitSet -> IO LitSet
minimizeConflictClauseLocal solver lits = do
  let xs = IS.toAscList lits
  ys <- filterM (liftM not . isRedundant) xs
  when debugMode $ do
    log solver "minimizeConflictClauseLocal:"
    log solver $ show xs
    log solver $ show ys
  return $ IS.fromAscList $ ys

  where
    isRedundant :: Lit -> IO Bool
    isRedundant lit = do
      c <- varReason solver (litVar lit)
      case c of
        Nothing -> return False
        Just c2 -> do
          ls <- reasonOf solver c2 (Just (litNot lit))
          allM test ls

    test :: Lit -> IO Bool
    test lit = do
      lv <- litLevel solver lit
      return $ lv == levelRoot || lit `IS.member` lits

minimizeConflictClauseRecursive :: Solver -> LitSet -> IO LitSet
minimizeConflictClauseRecursive solver lits = do
  let
    isRedundant :: Lit -> IO Bool
    isRedundant lit = do
      c <- varReason solver (litVar lit)
      case c of
        Nothing -> return False
        Just c2 -> do
          ls <- reasonOf solver c2 (Just (litNot lit))
          go ls IS.empty

    go :: [Lit] -> IS.IntSet -> IO Bool
    go [] _ = return True
    go (lit : ls) seen = do
      lv <- litLevel solver lit
      if lv == levelRoot || lit `IS.member` lits || lit `IS.member` seen then
        go ls seen
      else do
        c <- varReason solver (litVar lit)
        case c of
          Nothing -> return False
          Just c2 -> do
            ls2 <- reasonOf solver c2 (Just (litNot lit))
            go (ls2 ++ ls) (IS.insert lit seen)

  let xs = IS.toAscList lits
  ys <- filterM (liftM not . isRedundant) xs
  when debugMode $ do
    log solver "minimizeConflictClauseRecursive:"
    log solver $ show xs
    log solver $ show ys
  return $ IS.fromAscList $ ys

popTrail :: Solver -> IO Lit
popTrail solver = do
  m <- readIORef (svTrail solver)
  case m of
    []   -> error "ToySolver.SAT.popTrail: empty trail"
    l:ls -> do
      writeIORef (svTrail solver) ls
      return l

-- | Revert to the state at given level
-- (keeping all assignment at @level@ but not beyond).
backtrackTo :: Solver -> Int -> IO ()
backtrackTo solver level = do
  when debugMode $ log solver $ printf "backtrackTo: %d" level
  writeIORef (svTrail solver) =<< loop =<< readIORef (svTrail solver)
  SQ.clear (svBCPQueue solver)
  writeIORef (svLevel solver) level
  where
    loop :: [Lit] -> IO [Lit]
    loop [] = return []
    loop lls@(l:ls) = do
      lv <- litLevel solver l
      if lv <= level
        then return lls
        else unassign solver (litVar l) >> loop ls

constructModel :: Solver -> IO ()
constructModel solver = do
  n <- nVars solver
  (marr::IOUArray Var Bool) <- newArray_ (1,n)
  forLoop 1 (<=n) (+1) $ \v -> do
    vd <- varData solver v
    a <- readIORef (vdAssignment vd)
    writeArray marr v (aValue (fromJust a))
  m <- unsafeFreeze marr
  writeIORef (svModel solver) (Just m)

constrDecayActivity :: Solver -> IO ()
constrDecayActivity solver = do
  d <- readIORef (svConstrDecay solver)
  modifyIORef' (svConstrInc solver) (d*)

constrBumpActivity :: ConstraintHandler a => Solver -> a -> IO ()
constrBumpActivity solver this = do
  aval <- constrReadActivity this
  when (aval >= 0) $ do -- learnt clause
    inc <- readIORef (svConstrInc solver)
    let aval2 = aval+inc
    constrWriteActivity this $! aval2
    when (aval2 > 1e20) $
      -- Rescale
      constrRescaleAllActivity solver

constrRescaleAllActivity :: Solver -> IO ()
constrRescaleAllActivity solver = do
  xs <- learntConstraints solver
  forM_ xs $ \c -> do
    aval <- constrReadActivity c
    when (aval >= 0) $
      constrWriteActivity c $! (aval * 1e-20)
  modifyIORef' (svConstrInc solver) (* 1e-20)

resetStat :: Solver -> IO ()
resetStat solver = do
  writeIORef (svNDecision solver) 0
  writeIORef (svNRandomDecision solver) 0
  writeIORef (svNConflict solver) 0
  writeIORef (svNRestart solver) 0
  writeIORef (svNLearntGC  solver) 0

printStatHeader :: Solver -> IO ()
printStatHeader solver = do
  log solver $ "============================[ Search Statistics ]============================"
  log solver $ " Time | Restart | Decision | Conflict |      LEARNT     | Fixed    | Removed "
  log solver $ "      |         |          |          |    Limit     GC | Var      | Constra "
  log solver $ "============================================================================="

printStat :: Solver -> Bool -> IO ()
printStat solver force = do
  nowWC <- getCurrentTime
  b <- if force
       then return True
       else do
         lastWC <- readIORef (svLastStatWC solver)
         return $ (nowWC `diffUTCTime` lastWC) > 1
  when b $ do
    startWC   <- readIORef (svStartWC solver)
    let tm = showTimeDiff $ nowWC `diffUTCTime` startWC
    restart   <- readIORef (svNRestart solver)
    dec       <- readIORef (svNDecision solver)
    conflict  <- readIORef (svNConflict solver)
    learntLim <- readIORef (svLearntLim solver)
    learntGC  <- readIORef (svNLearntGC solver)
    fixed     <- readIORef (svNFixed solver)
    removed   <- readIORef (svNRemovedConstr solver)
    log solver $ printf "%s | %7d | %8d | %8d | %8d %6d | %8d | %8d"
      tm restart dec conflict learntLim learntGC fixed removed
    writeIORef (svLastStatWC solver) nowWC

showTimeDiff :: NominalDiffTime -> String
showTimeDiff sec
  | si <  100  = printf "%4.1fs" (fromRational s :: Double)
  | si <= 9999 = printf "%4ds" si
  | mi <  100  = printf "%4.1fm" (fromRational m :: Double)
  | mi <= 9999 = printf "%4dm" mi
  | hi <  100  = printf "%4.1fs" (fromRational h :: Double)
  | otherwise  = printf "%4dh" hi
  where
    s :: Rational
    s = realToFrac sec

    si :: Integer
    si = round s

    m :: Rational
    m = s / 60

    mi :: Integer
    mi = round m

    h :: Rational
    h = m / 60

    hi :: Integer
    hi = round h

{--------------------------------------------------------------------
  constraint implementation
--------------------------------------------------------------------}

class (Eq a, Hashable a) => ConstraintHandler a where
  toConstraintHandler :: a -> SomeConstraintHandler

  showConstraintHandler :: Solver -> a -> IO String

  attach :: Solver -> a -> IO Bool

  watchedLiterals :: Solver -> a -> IO [Lit]

  watchedVariables :: Solver -> a -> IO [Var]

  -- | invoked with the watched literal when the literal is falsified.
  -- 'watch' で 'toConstraint' を呼び出して heap allocation が発生するのを
  -- 避けるために、元の 'SomeConstraintHandler' も渡しておく。
  basicPropagate :: Solver -> SomeConstraintHandler -> a -> Lit -> IO Bool

  -- | deduce a clause C∨l from the constraint and return C.
  -- C and l should be false and true respectively under the current
  -- assignment.
  basicReasonOf :: Solver -> a -> Maybe Lit -> IO Clause

  isPBRepresentable :: Solver -> a -> IO Bool
  toPBLinAtLeast :: Solver -> a -> IO PBLinAtLeast

  isSatisfied :: Solver -> a -> IO Bool

  constrIsProtected :: Solver -> a -> IO Bool
  constrIsProtected _ _ = return False

  constrWeight :: Solver -> a -> IO Double
  constrWeight _ _ = return 1.0

  constrReadActivity :: a -> IO Double

  constrWriteActivity :: a -> Double -> IO ()

detach :: ConstraintHandler a => Solver -> a -> IO ()
detach solver c = do
  let c2 = toConstraintHandler c
  lits <- watchedLiterals solver c
  forM_ lits $ \lit -> do
    ld <- litData solver lit
    modifyIORef' (ldWatches ld) (delete c2)
  vs <- watchedVariables solver c
  forM_ vs $ \v -> do
    vd <- varData solver v
    modifyIORef' (vdWatches vd) (delete c2)

  b <- isPBRepresentable solver c
  when b $ do
    (lhs,_) <- toPBLinAtLeast solver c
    forM_ lhs $ \(_,lit) -> do
      ld <- litData solver lit
      modifyIORef' (ldOccurList ld) (HashSet.delete c2)

-- | invoked with the watched literal when the literal is falsified.
propagate :: Solver -> SomeConstraintHandler -> Lit -> IO Bool
propagate solver c l = basicPropagate solver c c l

-- | deduce a clause C∨l from the constraint and return C.
-- C and l should be false and true respectively under the current
-- assignment.
reasonOf :: ConstraintHandler a => Solver -> a -> Maybe Lit -> IO Clause
reasonOf solver c x = do
  when debugMode $
    case x of
      Nothing -> return ()
      Just lit -> do
        val <- litValue solver lit
        unless (lTrue == val) $ do
          str <- showConstraintHandler solver c
          error (printf "reasonOf: value of literal %d should be True but %s (basicReasonOf %s %s)" lit (show val) str (show x))
  cl <- basicReasonOf solver c x
  when debugMode $ do
    forM_ cl $ \lit -> do
      val <- litValue solver lit
      unless (lFalse == val) $ do
        str <- showConstraintHandler solver c
        error (printf "reasonOf: value of literal %d should be False but %s (basicReasonOf %s %s)" lit (show val) str (show x))
  return cl

isLocked :: Solver -> SomeConstraintHandler -> IO Bool
isLocked solver c = do
    b1 <- anyM p1 =<< watchedLiterals solver c
    b2 <- anyM p2 =<< watchedVariables solver c
    return $ b1 || b2
  where
    p1 :: Lit -> IO Bool
    p1 lit = do
      val <- litValue solver lit
      if val /= lTrue then return False
      else do
        m <- varReason solver (litVar lit)
        case m of
          Nothing -> return False
          Just c2 -> return $! c == c2
    p2 :: Var -> IO Bool
    p2 var = do
      val <- varValue solver var
      if val == lUndef then return False
      else do
        m <- varReason solver var
        case m of
          Nothing -> return False
          Just c2 -> return $! c == c2

data SomeConstraintHandler
  = CHClause !ClauseHandler
  | CHAtLeast !AtLeastHandler
  | CHPBCounter !PBHandlerCounter
  | CHPBPueblo !PBHandlerPueblo
  deriving Eq

instance Hashable SomeConstraintHandler where
  hashWithSalt s (CHClause c)    = s `hashWithSalt` (0::Int) `hashWithSalt` c
  hashWithSalt s (CHAtLeast c)   = s `hashWithSalt` (1::Int) `hashWithSalt` c
  hashWithSalt s (CHPBCounter c) = s `hashWithSalt` (2::Int) `hashWithSalt` c
  hashWithSalt s (CHPBPueblo c)  = s `hashWithSalt` (3::Int) `hashWithSalt` c

instance ConstraintHandler SomeConstraintHandler where
  toConstraintHandler = id

  showConstraintHandler solver (CHClause c)    = showConstraintHandler solver c
  showConstraintHandler solver (CHAtLeast c)   = showConstraintHandler solver c
  showConstraintHandler solver (CHPBCounter c) = showConstraintHandler solver c
  showConstraintHandler solver (CHPBPueblo c)  = showConstraintHandler solver c

  attach solver (CHClause c)    = attach solver c
  attach solver (CHAtLeast c)   = attach solver c
  attach solver (CHPBCounter c) = attach solver c
  attach solver (CHPBPueblo c)  = attach solver c

  watchedLiterals solver (CHClause c)    = watchedLiterals solver c
  watchedLiterals solver (CHAtLeast c)   = watchedLiterals solver c
  watchedLiterals solver (CHPBCounter c) = watchedLiterals solver c
  watchedLiterals solver (CHPBPueblo c)  = watchedLiterals solver c

  watchedVariables solver (CHClause c)    = watchedVariables solver c
  watchedVariables solver (CHAtLeast c)   = watchedVariables solver c
  watchedVariables solver (CHPBCounter c) = watchedVariables solver c
  watchedVariables solver (CHPBPueblo c)  = watchedVariables solver c

  basicPropagate solver this (CHClause c)  lit   = basicPropagate solver this c lit
  basicPropagate solver this (CHAtLeast c) lit   = basicPropagate solver this c lit
  basicPropagate solver this (CHPBCounter c) lit = basicPropagate solver this c lit
  basicPropagate solver this (CHPBPueblo c) lit  = basicPropagate solver this c lit

  basicReasonOf solver (CHClause c)  l   = basicReasonOf solver c l
  basicReasonOf solver (CHAtLeast c) l   = basicReasonOf solver c l
  basicReasonOf solver (CHPBCounter c) l = basicReasonOf solver c l
  basicReasonOf solver (CHPBPueblo c) l  = basicReasonOf solver c l

  isPBRepresentable solver (CHClause c)    = isPBRepresentable solver c
  isPBRepresentable solver (CHAtLeast c)   = isPBRepresentable solver c
  isPBRepresentable solver (CHPBCounter c) = isPBRepresentable solver c
  isPBRepresentable solver (CHPBPueblo c)  = isPBRepresentable solver c

  toPBLinAtLeast solver (CHClause c)    = toPBLinAtLeast solver c
  toPBLinAtLeast solver (CHAtLeast c)   = toPBLinAtLeast solver c
  toPBLinAtLeast solver (CHPBCounter c) = toPBLinAtLeast solver c
  toPBLinAtLeast solver (CHPBPueblo c)  = toPBLinAtLeast solver c

  isSatisfied solver (CHClause c)    = isSatisfied solver c
  isSatisfied solver (CHAtLeast c)   = isSatisfied solver c
  isSatisfied solver (CHPBCounter c) = isSatisfied solver c
  isSatisfied solver (CHPBPueblo c)  = isSatisfied solver c

  constrIsProtected solver (CHClause c)    = constrIsProtected solver c
  constrIsProtected solver (CHAtLeast c)   = constrIsProtected solver c
  constrIsProtected solver (CHPBCounter c) = constrIsProtected solver c
  constrIsProtected solver (CHPBPueblo c)  = constrIsProtected solver c

  constrReadActivity (CHClause c)    = constrReadActivity c
  constrReadActivity (CHAtLeast c)   = constrReadActivity c
  constrReadActivity (CHPBCounter c) = constrReadActivity c
  constrReadActivity (CHPBPueblo c)  = constrReadActivity c

  constrWriteActivity (CHClause c)    aval = constrWriteActivity c aval
  constrWriteActivity (CHAtLeast c)   aval = constrWriteActivity c aval
  constrWriteActivity (CHPBCounter c) aval = constrWriteActivity c aval
  constrWriteActivity (CHPBPueblo c)  aval = constrWriteActivity c aval

-- To avoid heap-allocation Maybe value, it returns -1 when not found.
findForWatch :: Solver -> IOUArray Int Lit -> Int -> Int -> IO Int
#ifndef __GLASGOW_HASKELL__
findForWatch solver a beg end = go beg end
  where
    go :: Int -> Int -> IO Int
    go i end | i > end = return (-1)
    go i end = do
      val <- litValue s =<< unsafeRead a i
      if val /= lFalse
        then return i
        else go (i+1) end
#else
{- We performed worker-wrapper transfomation manually, since the worker
   generated by GHC has type
   "Int# -> Int# -> State# RealWorld -> (# State# RealWorld, Int #)",
   not "Int# -> Int# -> State# RealWorld -> (# State# RealWorld, Int# #)".
   We want latter one to avoid heap-allocating Int value. -}
findForWatch solver a (I# beg) (I# end) = IO $ \w ->
  case go# beg end w of
    (# w2, ret #) -> (# w2, I# ret #)
  where
    go# :: Int# -> Int# -> State# RealWorld -> (# State# RealWorld, Int# #)
#if __GLASGOW_HASKELL__ < 708
    go# i end w | i ># end = (# w, -1# #)
#else
    go# i end w | isTrue# (i ># end) = (# w, -1# #)
#endif
    go# i end w =
      case unIO (litValue solver =<< unsafeRead a (I# i)) w of
        (# w2, val #) ->
          if val /= lFalse
            then (# w2, i #)
            else go# (i +# 1#) end w2

    unIO (IO f) = f
#endif

{--------------------------------------------------------------------
  Clause
--------------------------------------------------------------------}

data ClauseHandler
  = ClauseHandler
  { claLits :: !(IOUArray Int Lit)
  , claActivity :: !(IORef Double)
  , claHash :: !Int
  }

instance Eq ClauseHandler where
  (==) = (==) `on` claLits

instance Hashable ClauseHandler where
  hash = claHash
  hashWithSalt = defaultHashWithSalt

newClauseHandler :: Clause -> Bool -> IO ClauseHandler
newClauseHandler ls learnt = do
  let size = length ls
  a <- newListArray (0, size-1) ls
  act <- newIORef $! (if learnt then 0 else -1)
  return (ClauseHandler a act (hash ls))

instance ConstraintHandler ClauseHandler where
  toConstraintHandler = CHClause

  showConstraintHandler _ this = do
    lits <- getElems (claLits this)
    return (show lits)

  attach solver this = do
    -- BCP Queue should be empty at this point.
    -- If not, duplicated propagation happens.
    bcpCheckEmpty solver

    (lb,ub) <- getBounds (claLits this)
    assert (lb == 0) $ return ()
    let size = ub-lb+1

    if size == 0 then do
      markBad solver
      return False
    else if size == 1 then do
      lit0 <- unsafeRead (claLits this) 0
      assignBy solver lit0 this
    else do
      ref <- newIORef 1
      let f i = do
            lit_i <- unsafeRead (claLits this) i
            val_i <- litValue solver lit_i
            if val_i /= lFalse then
              return True
            else do
              j <- readIORef ref
              k <- findForWatch solver (claLits this) j ub
              case k of
                -1 -> do
                  return False
                _ -> do
                  lit_k <- unsafeRead (claLits this) k
                  unsafeWrite (claLits this) i lit_k
                  unsafeWrite (claLits this) k lit_i
                  writeIORef ref $! (k+1)
                  return True

      b <- f 0
      if b then do
        lit0 <- unsafeRead (claLits this) 0
        watch solver lit0 this
        b2 <- f 1
        if b2 then do
          lit1 <- unsafeRead (claLits this) 1
          watch solver lit1 this
          return True
        else do -- UNIT
          -- We need to watch the most recently falsified literal
          (i,_) <- liftM (maximumBy (comparing snd)) $ forM [1..ub] $ \l -> do
            lit <- unsafeRead (claLits this) l
            lv <- litLevel solver lit
            return (l,lv)
          lit1 <- unsafeRead (claLits this) 1
          liti <- unsafeRead (claLits this) i
          unsafeWrite (claLits this) 1 liti
          unsafeWrite (claLits this) i lit1
          watch solver liti this
          assignBy solver lit0 this -- should always succeed
      else do -- CONFLICT
        ls <- liftM (map fst . sortBy (flip (comparing snd))) $ forM [lb..ub] $ \l -> do
          lit <- unsafeRead (claLits this) l
          lv <- litLevel solver lit
          return (l,lv)
        forM_ (zip [0..] ls) $ \(i,lit) -> do
          unsafeWrite (claLits this) i lit
        lit0 <- unsafeRead (claLits this) 0
        lit1 <- unsafeRead (claLits this) 1
        watch solver lit0 this
        watch solver lit1 this
        return False

  watchedLiterals _ this = do
    lits <- getElems (claLits this)
    case lits of
      l1:l2:_ -> return [l1, l2]
      _ -> return []

  watchedVariables _ _ = return []

  basicPropagate !solver this this2 !falsifiedLit = do
    preprocess

    !lit0 <- unsafeRead a 0
    !val0 <- litValue solver lit0
    if val0 == lTrue then do
      watch solver falsifiedLit this
      return True
    else do
      (!lb,!ub) <- getBounds a
      assert (lb==0) $ return ()
      i <- findForWatch solver a 2 ub
      case i of
        -1 -> do
          when debugMode $ logIO solver $ do
             str <- showConstraintHandler solver this
             return $ printf "basicPropagate: %s is unit" str
          watch solver falsifiedLit this
          assignBy solver lit0 this
        _  -> do
          !lit1 <- unsafeRead a 1
          !liti <- unsafeRead a i
          unsafeWrite a 1 liti
          unsafeWrite a i lit1
          watch solver liti this
          return True

    where
      a = claLits this2

      preprocess :: IO ()
      preprocess = do
        !l0 <- unsafeRead a 0
        !l1 <- unsafeRead a 1
        assert (l0==falsifiedLit || l1==falsifiedLit) $ return ()
        when (l0==falsifiedLit) $ do
          unsafeWrite a 0 l1
          unsafeWrite a 1 l0

  basicReasonOf _ this l = do
    lits <- getElems (claLits this)
    case l of
      Nothing -> return lits
      Just lit -> do
        assert (lit == head lits) $ return ()
        return $ tail lits

  isPBRepresentable _ _ = return True

  toPBLinAtLeast _ this = do
    lits <- getElems (claLits this)
    return ([(1,l) | l <- lits], 1)

  isSatisfied solver this = do
    lits <- getElems (claLits this)
    vals <- mapM (litValue solver) lits
    return $ lTrue `elem` vals

  constrIsProtected _ this = do
    size <- liftM rangeSize (getBounds (claLits this))
    return $! size <= 2

  constrReadActivity this = readIORef (claActivity this)

  constrWriteActivity this aval = writeIORef (claActivity this) $! aval

instantiateClause :: Solver -> Clause -> IO (Maybe Clause)
instantiateClause solver = loop []
  where
    loop :: [Lit] -> [Lit] -> IO (Maybe Clause)
    loop ret [] = return $ Just ret
    loop ret (l:ls) = do
      val <- litValue solver l
      if val==lTrue then
        return Nothing
      else if val==lFalse then
        loop ret ls
      else
        loop (l : ret) ls

basicAttachClauseHandler :: Solver -> ClauseHandler -> IO Bool
basicAttachClauseHandler solver this = do
  lits <- getElems (claLits this)
  case lits of
    [] -> do
      markBad solver
      return False
    [l1] -> do
      assignBy solver l1 this
    l1:l2:_ -> do
      watch solver l1 this
      watch solver l2 this
      return True

{--------------------------------------------------------------------
  Cardinality Constraint
--------------------------------------------------------------------}

data AtLeastHandler
  = AtLeastHandler
  { atLeastLits :: IOUArray Int Lit
  , atLeastNum :: !Int
  , atLeastActivity :: !(IORef Double)
  , atLeastHash :: !Int
  }

instance Eq AtLeastHandler where
  (==) = (==) `on` atLeastLits

instance Hashable AtLeastHandler where
  hash = atLeastHash
  hashWithSalt = defaultHashWithSalt

newAtLeastHandler :: [Lit] -> Int -> Bool -> IO AtLeastHandler
newAtLeastHandler ls n learnt = do
  let size = length ls
  a <- newListArray (0, size-1) ls
  act <- newIORef $! (if learnt then 0 else -1)
  return (AtLeastHandler a n act (hash (ls,n)))

instance ConstraintHandler AtLeastHandler where
  toConstraintHandler = CHAtLeast

  showConstraintHandler _ this = do
    lits <- getElems (atLeastLits this)
    return $ show lits ++ " >= " ++ show (atLeastNum this)

  -- FIXME: simplify implementation
  attach solver this = do
    -- BCP Queue should be empty at this point.
    -- If not, duplicated propagation happens.
    bcpCheckEmpty solver

    let a = atLeastLits this
    (lb,ub) <- getBounds a
    assert (lb == 0) $ return ()
    let m = ub - lb + 1
        n = atLeastNum this

    if m < n then do
      markBad solver
      return False
    else if m == n then do
      let f i = do
            lit <- unsafeRead a i
            assignBy solver lit this
      allM f [0..n-1]
    else do -- m > n
      let f !i !j
            | i == n = do
                -- NOT VIOLATED: n literals (0 .. n-1) are watched
                k <- findForWatch solver a j ub
                if k /= -1 then do
                  -- NOT UNIT
                  lit_n <- unsafeRead a n
                  lit_k <- unsafeRead a k
                  unsafeWrite a n lit_k
                  unsafeWrite a k lit_n
                  watch solver lit_k this
                  -- n+1 literals (0 .. n) are watched.
                else do
                  -- UNIT
                  forLoop 0 (<n) (+1) $ \l -> do
                    lit <- unsafeRead a l
                    _ <- assignBy solver lit this -- should always succeed
                    return ()
                  -- We need to watch the most recently falsified literal
                  (l,_) <- liftM (maximumBy (comparing snd)) $ forM [n..ub] $ \l -> do
                    lit <- unsafeRead a l
                    lv <- litLevel solver lit
                    when debugMode $ do
                      val <- litValue solver lit
                      unless (val == lFalse) $ error "AtLeastHandler.attach: should not happen"
                    return (l,lv)
                  lit_n <- unsafeRead a n
                  lit_l <- unsafeRead a l
                  unsafeWrite a n lit_l
                  unsafeWrite a l lit_n
                  watch solver lit_l this
                  -- n+1 literals (0 .. n) are watched.
                return True
            | otherwise = do
                assert (i < n && n <= j) $ return ()
                lit_i <- unsafeRead a i
                val_i <- litValue solver lit_i
                if val_i /= lFalse then do
                  watch solver lit_i this
                  f (i+1) j
                else do
                  k <- findForWatch solver a j ub
                  if k /= -1 then do
                    lit_k <- unsafeRead a k
                    unsafeWrite a i lit_k
                    unsafeWrite a k lit_i
                    watch solver lit_k this
                    f (i+1) (k+1)
                  else do
                    -- CONFLICT
                    -- We need to watch unassigned literals or most recently falsified literals.
                    do xs <- liftM (sortBy (flip (comparing snd))) $ forM [i..ub] $ \l -> do
                         lit <- readArray a l
                         val <- litValue solver lit
                         if val == lFalse then do
                           lv <- litLevel solver lit
                           return (lit, lv)
                         else do
                           return (lit, maxBound)
                       forM_ (zip [i..ub] xs) $ \(l,(lit,_lv)) -> do
                         writeArray a l lit
                    forLoop i (<=n) (+1) $ \l -> do
                      lit_l <- readArray a l
                      watch solver lit_l this
                    -- n+1 literals (0 .. n) are watched.
                    return False
      f 0 n

  watchedLiterals _ this = do
    lits <- getElems (atLeastLits this)
    let n = atLeastNum this
    let ws = if length lits > n then take (n+1) lits else []
    return ws

  watchedVariables _ _ = return []

  basicPropagate solver this this2 falsifiedLit = do
    preprocess

    when debugMode $ do
      litn <- readArray a n
      unless (litn == falsifiedLit) $ error "AtLeastHandler.basicPropagate: should not happen"

    (lb,ub) <- getBounds a
    assert (lb==0) $ return ()
    i <- findForWatch solver a (n+1) ub
    case i of
      -1 -> do
        when debugMode $ logIO solver $ do
          str <- showConstraintHandler solver this
          return $ printf "basicPropagate: %s is unit" str
        watch solver falsifiedLit this
        let loop :: Int -> IO Bool
            loop i
              | i >= n = return True
              | otherwise = do
                  liti <- unsafeRead a i
                  ret2 <- assignBy solver liti this
                  if ret2
                    then loop (i+1)
                    else return False
        loop 0
      _ -> do
        liti <- unsafeRead a i
        litn <- unsafeRead a n
        unsafeWrite a i litn
        unsafeWrite a n liti
        watch solver liti this
        return True

    where
      a = atLeastLits this2
      n = atLeastNum this2

      preprocess :: IO ()
      preprocess = loop 0
        where
          loop :: Int -> IO ()
          loop i
            | i >= n = return ()
            | otherwise = do
              li <- unsafeRead a i
              if (li /= falsifiedLit) then
                loop (i+1)
              else do
                ln <- unsafeRead a n
                unsafeWrite a n li
                unsafeWrite a i ln

  basicReasonOf solver this concl = do
    (lb,ub) <- getBounds (atLeastLits this)
    assert (lb==0) $ return ()
    let n = atLeastNum this
    falsifiedLits <- mapM (readArray (atLeastLits this)) [n..ub] -- drop first n elements
    when debugMode $ do
      forM_ falsifiedLits $ \lit -> do
        val <- litValue solver lit
        unless (val == lFalse) $ do
          error $ printf "AtLeastHandler.basicReasonOf: %d is %s (lFalse expected)" lit (show val)
    case concl of
      Nothing -> do
        let go :: Int -> IO Lit
            go i
              | i >= n = error $ printf "AtLeastHandler.basicReasonOf: cannot find falsified literal in first %d elements" n
              | otherwise = do
                  lit <- readArray (atLeastLits this) i
                  val <- litValue solver lit
                  if val == lFalse
                  then return lit
                  else go (i+1)
        lit <- go lb
        return $ lit : falsifiedLits
      Just lit -> do
        when debugMode $ do
          es <- getElems (atLeastLits this)
          unless (lit `elem` take n es) $
            error $ printf "AtLeastHandler.basicReasonOf: cannot find %d in first %d elements" n
        return falsifiedLits

  isPBRepresentable _ _ = return True

  toPBLinAtLeast _ this = do
    lits <- getElems (atLeastLits this)
    return ([(1,l) | l <- lits], fromIntegral (atLeastNum this))

  isSatisfied solver this = do
    lits <- getElems (atLeastLits this)
    vals <- mapM (litValue solver) lits
    return $ length [v | v <- vals, v == lTrue] >= atLeastNum this

  constrReadActivity this = readIORef (atLeastActivity this)

  constrWriteActivity this aval = writeIORef (atLeastActivity this) $! aval

instantiateAtLeast :: Solver -> AtLeast -> IO AtLeast
instantiateAtLeast solver (xs,n) = loop ([],n) xs
  where
    loop :: AtLeast -> [Lit] -> IO AtLeast
    loop ret [] = return ret
    loop (ys,m) (l:ls) = do
      val <- litValue solver l
      if val == lTrue then
        loop (ys, m-1) ls
      else if val == lFalse then
        loop (ys, m) ls
      else
        loop (l:ys, m) ls

basicAttachAtLeastHandler :: Solver -> AtLeastHandler -> IO Bool
basicAttachAtLeastHandler solver this = do
  lits <- getElems (atLeastLits this)
  let m = length lits
      n = atLeastNum this
  if m < n then do
    markBad solver
    return False
  else if m == n then do
    allM (\l -> assignBy solver l this) lits
  else do -- m > n
    forM_ (take (n+1) lits) $ \l -> watch solver l this
    return True

{--------------------------------------------------------------------
  Pseudo Boolean Constraint
--------------------------------------------------------------------}

newPBHandler :: Solver -> PBLinSum -> Integer -> Bool -> IO SomeConstraintHandler
newPBHandler solver ts degree learnt = do
  config <- readIORef (svPBHandlerType solver)
  case config of
    PBHandlerTypeCounter -> do
      c <- newPBHandlerCounter ts degree learnt
      return (toConstraintHandler c)
    PBHandlerTypePueblo -> do
      c <- newPBHandlerPueblo ts degree learnt
      return (toConstraintHandler c)

newPBHandlerPromoted :: Solver -> PBLinSum -> Integer -> Bool -> IO SomeConstraintHandler
newPBHandlerPromoted solver lhs rhs learnt = do
  case pbToAtLeast (lhs,rhs) of
    Nothing -> newPBHandler solver lhs rhs learnt
    Just (lhs2, rhs2) -> do
      if rhs2 /= 1 then do
        h <- newAtLeastHandler lhs2 rhs2 learnt
        return $ toConstraintHandler h
      else do
        h <- newClauseHandler lhs2 learnt
        return $ toConstraintHandler h

instantiatePB :: Solver -> PBLinAtLeast -> IO PBLinAtLeast
instantiatePB solver (xs,n) = loop ([],n) xs
  where
    loop :: PBLinAtLeast -> PBLinSum -> IO PBLinAtLeast
    loop ret [] = return ret
    loop (ys,m) ((c,l):ts) = do
      val <- litValue solver l
      if val == lTrue then
        loop (ys, m-c) ts
      else if val == lFalse then
        loop (ys, m) ts
      else
        loop ((c,l):ys, m) ts

pbOverSAT :: Solver -> PBLinAtLeast -> IO Bool
pbOverSAT solver (lhs, rhs) = do
  ss <- forM lhs $ \(c,l) -> do
    v <- litValue solver l
    if v /= lFalse
      then return c
      else return 0
  return $! sum ss > rhs

pbToAtLeast :: PBLinAtLeast -> Maybe AtLeast
pbToAtLeast (lhs, rhs) = do
  let cs = [c | (c,_) <- lhs]
  guard $ Set.size (Set.fromList cs) == 1
  let c = head cs
  return $ (map snd lhs, fromInteger ((rhs+c-1) `div` c))

{--------------------------------------------------------------------
  Pseudo Boolean Constraint (Counter)
--------------------------------------------------------------------}   

data PBHandlerCounter
  = PBHandlerCounter
  { pbTerms    :: !PBLinSum -- sorted in the decending order on coefficients.
  , pbDegree   :: !Integer
  , pbCoeffMap :: !(LitMap Integer)
  , pbMaxSlack :: !Integer
  , pbSlack    :: !(IORef Integer)
  , pbActivity :: !(IORef Double)
  , pbHash     :: !Int
  }

instance Eq PBHandlerCounter where
  (==) = (==) `on` pbSlack

instance Hashable PBHandlerCounter where
  hash = pbHash
  hashWithSalt = defaultHashWithSalt

newPBHandlerCounter :: PBLinSum -> Integer -> Bool -> IO PBHandlerCounter
newPBHandlerCounter ts degree learnt = do
  let ts' = sortBy (flip compare `on` fst) ts
      slack = sum (map fst ts) - degree      
      m = IM.fromList [(l,c) | (c,l) <- ts]
  s <- newIORef slack
  act <- newIORef $! (if learnt then 0 else -1)
  return (PBHandlerCounter ts' degree m slack s act (hash (ts,degree)))

instance ConstraintHandler PBHandlerCounter where
  toConstraintHandler = CHPBCounter

  showConstraintHandler _ this = do
    return $ show (pbTerms this) ++ " >= " ++ show (pbDegree this)

  attach solver this = do
    -- BCP queue should be empty at this point.
    -- It is important for calculating slack.
    bcpCheckEmpty solver
    s <- liftM sum $ forM (pbTerms this) $ \(c,l) -> do
      watch solver l this
      val <- litValue solver l
      if val == lFalse then do
        addBacktrackCB solver (litVar l) $ modifyIORef' (pbSlack this) (+ c)
        return 0
      else do
        return c
    let slack = s - pbDegree this
    writeIORef (pbSlack this) $! slack
    if slack < 0 then
      return False
    else do
      flip allM (pbTerms this) $ \(c,l) -> do
        val <- litValue solver l
        if c > slack && val == lUndef then do
          assignBy solver l this
        else
          return True

  watchedLiterals _ this = do
    return $ map snd $ pbTerms this

  watchedVariables _ _ = return []

  basicPropagate solver this this2 falsifiedLit = do
    watch solver falsifiedLit this
    let c = pbCoeffMap this2 IM.! falsifiedLit
    modifyIORef' (pbSlack this2) (subtract c)
    addBacktrackCB solver (litVar falsifiedLit) $ modifyIORef' (pbSlack this2) (+ c)
    s <- readIORef (pbSlack this2)
    if s < 0 then
      return False
    else do
      forM_ (takeWhile (\(c1,_) -> c1 > s) (pbTerms this2)) $ \(_,l1) -> do
        v <- litValue solver l1
        when (v == lUndef) $ do
          assignBy solver l1 this
          return ()
      return True

  basicReasonOf solver this l = do
    case l of
      Nothing -> do
        let p _ = return True
        f p (pbMaxSlack this) (pbTerms this)
      Just lit -> do
        idx <- varAssignNo solver (litVar lit)
        -- PB制約の場合には複数回unitになる可能性があり、
        -- litへの伝播以降に割り当てられたリテラルを含まないよう注意が必要
        let p lit2 =do
              idx2 <- varAssignNo solver (litVar lit2)
              return $ idx2 < idx
        let c = pbCoeffMap this IM.! lit
        f p (pbMaxSlack this - c) (pbTerms this)
    where
      {-# INLINE f #-}
      f :: (Lit -> IO Bool) -> Integer -> PBLinSum -> IO [Lit]
      f p s xs = go s xs []
        where
          go :: Integer -> PBLinSum -> [Lit] -> IO [Lit]
          go s _ ret | s < 0 = return ret
          go _ [] _ = error "PBHandlerCounter.basicReasonOf: should not happen"
          go s ((c,lit):xs) ret = do
            val <- litValue solver lit
            if val == lFalse then do
              b <- p lit
              if b
              then go (s - c) xs (lit:ret)
              else go s xs ret
            else do
              go s xs ret

  isPBRepresentable _ _ = return True

  toPBLinAtLeast _ this = do
    return (pbTerms this, pbDegree this)

  isSatisfied solver this = do
    xs <- forM (pbTerms this) $ \(c,l) -> do
      v <- litValue solver l
      if v == lTrue
        then return c
        else return 0
    return $ sum xs >= pbDegree this

  constrWeight _ _ = return 0.5

  constrReadActivity this = readIORef (pbActivity this)

  constrWriteActivity this aval = writeIORef (pbActivity this) $! aval

{--------------------------------------------------------------------
  Pseudo Boolean Constraint (Pueblo)
--------------------------------------------------------------------}

data PBHandlerPueblo
  = PBHandlerPueblo
  { puebloTerms     :: !PBLinSum
  , puebloDegree    :: !Integer
  , puebloMaxSlack  :: !Integer
  , puebloWatches   :: !(IORef LitSet)
  , puebloWatchSum  :: !(IORef Integer)
  , puebloActivity  :: !(IORef Double)
  , puebloHash      :: !Int
  }

instance Eq PBHandlerPueblo where
  (==) = (==) `on` puebloWatchSum

instance Hashable PBHandlerPueblo where
  hash = puebloHash
  hashWithSalt = defaultHashWithSalt

puebloAMax :: PBHandlerPueblo -> Integer
puebloAMax this =
  case puebloTerms this of
    (c,_):_ -> c
    [] -> 0 -- should not happen?

newPBHandlerPueblo :: PBLinSum -> Integer -> Bool -> IO PBHandlerPueblo
newPBHandlerPueblo ts degree learnt = do
  let ts' = sortBy (flip compare `on` fst) ts
      slack = sum [c | (c,_) <- ts'] - degree
  ws   <- newIORef IS.empty
  wsum <- newIORef 0
  act  <- newIORef $! (if learnt then 0 else -1)
  return $ PBHandlerPueblo ts' degree slack ws wsum act (hash (ts,degree))

puebloGetWatchSum :: PBHandlerPueblo -> IO Integer
puebloGetWatchSum pb = readIORef (puebloWatchSum pb)

puebloWatch :: Solver -> SomeConstraintHandler -> PBHandlerPueblo -> PBLinTerm -> IO ()
puebloWatch solver constr !pb (c, lit) = do
  watch solver lit constr
  modifyIORef' (puebloWatches pb) (IS.insert lit)
  modifyIORef' (puebloWatchSum pb) (+c)

puebloUnwatch :: Solver -> PBHandlerPueblo -> PBLinTerm -> IO ()
puebloUnwatch _solver pb (c, lit) = do
  modifyIORef' (puebloWatches pb) (IS.delete lit)
  modifyIORef' (puebloWatchSum pb) (subtract c)

instance ConstraintHandler PBHandlerPueblo where
  toConstraintHandler = CHPBPueblo

  showConstraintHandler _ this = do
    return $ show (puebloTerms this) ++ " >= " ++ show (puebloDegree this)

  attach solver this = do
    bcpCheckEmpty solver
    let constr = toConstraintHandler this
    ret <- puebloPropagate solver constr this

    -- register to watch recently falsified literals to recover
    -- "WatchSum >= puebloDegree this + puebloAMax this" when backtrack is performed.
    wsum <- puebloGetWatchSum this
    unless (wsum >= puebloDegree this + puebloAMax this) $ do
      let f m tm@(_,lit) = do
            val <- litValue solver lit
            if val == lFalse then do
              idx <- varAssignNo solver (litVar lit)
              return (IM.insert idx tm m)
            else
              return m
#if MIN_VERSION_containers(0,5,0)
      xs <- liftM (map snd . IM.toDescList) $ foldM f IM.empty (puebloTerms this)
#else
      xs <- liftM (reverse . map snd . IM.toAscList) $ foldM f IM.empty (puebloTerms this)
#endif
      let g !_ [] = return ()
          g !s (t@(c,l):ts) = do
            addBacktrackCB solver (litVar l) $ puebloWatch solver constr this t
            if s+c >= puebloDegree this + puebloAMax this then return ()
            else g (s+c) ts
      g wsum xs

    return ret

  watchedLiterals _ this = liftM IS.toList $ readIORef (puebloWatches this)

  watchedVariables _ _ = return []

  basicPropagate solver this this2 falsifiedLit = do
    let t = fromJust $ find (\(_,l) -> l==falsifiedLit) (puebloTerms this2)
    puebloUnwatch solver this2 t
    ret <- puebloPropagate solver this this2
    wsum <- puebloGetWatchSum this2
    unless (wsum >= puebloDegree this2 + puebloAMax this2) $
      addBacktrackCB solver (litVar falsifiedLit) $ puebloWatch solver this this2 t
    return ret

  basicReasonOf solver this l = do
    case l of
      Nothing -> do
        let p _ = return True
        f p (puebloMaxSlack this) (puebloTerms this)
      Just lit -> do
        idx <- varAssignNo solver (litVar lit)
        -- PB制約の場合には複数回unitになる可能性があり、
        -- litへの伝播以降に割り当てられたリテラルを含まないよう注意が必要
        let p lit2 =do
              idx2 <- varAssignNo solver (litVar lit2)
              return $ idx2 < idx
        let c = fst $ fromJust $ find (\(_,l) -> l == lit) (puebloTerms this)
        f p (puebloMaxSlack this - c) (puebloTerms this)
    where
      {-# INLINE f #-}
      f :: (Lit -> IO Bool) -> Integer -> PBLinSum -> IO [Lit]
      f p s xs = go s xs []
        where
          go :: Integer -> PBLinSum -> [Lit] -> IO [Lit]
          go s _ ret | s < 0 = return ret
          go _ [] _ = error "PBHandlerPueblo.basicReasonOf: should not happen"
          go s ((c,lit):xs) ret = do
            val <- litValue solver lit
            if val == lFalse then do
              b <- p lit
              if b
              then go (s - c) xs (lit:ret)
              else go s xs ret
            else do
              go s xs ret

  isPBRepresentable _ _ = return True

  toPBLinAtLeast _ this = do
    return (puebloTerms this, puebloDegree this)

  isSatisfied solver this = do
    xs <- forM (puebloTerms this) $ \(c,l) -> do
      v <- litValue solver l
      if v == lTrue
        then return c
        else return 0
    return $ sum xs >= puebloDegree this

  constrWeight _ _ = return 0.5

  constrReadActivity this = readIORef (puebloActivity this)

  constrWriteActivity this aval = writeIORef (puebloActivity this) $! aval

puebloPropagate :: Solver -> SomeConstraintHandler -> PBHandlerPueblo -> IO Bool
puebloPropagate solver constr this = do
  puebloUpdateWatchSum solver constr this
  watchsum <- puebloGetWatchSum this
  if puebloDegree this + puebloAMax this <= watchsum then
    return True
  else if watchsum < puebloDegree this then do
    -- CONFLICT
    return False
  else do -- puebloDegree this <= watchsum < puebloDegree this + puebloAMax this
    -- UNIT PROPAGATION
    let f [] = return True
        f ((c,lit) : ts) = do
          watchsum <- puebloGetWatchSum this
          if watchsum - c >= puebloDegree this then
            return True
          else do
            val <- litValue solver lit
            when (val == lUndef) $ do
              b <- assignBy solver lit this
              assert b $ return ()
            f ts
    f $ puebloTerms this

puebloUpdateWatchSum :: Solver -> SomeConstraintHandler -> PBHandlerPueblo -> IO ()
puebloUpdateWatchSum solver constr this = do
  let f [] = return ()
      f (t@(_,lit):ts) = do
        watchSum <- puebloGetWatchSum this
        if watchSum >= puebloDegree this + puebloAMax this then
          return ()
        else do
          val <- litValue solver lit
          watched <- liftM (lit `IS.member`) $ readIORef (puebloWatches this)
          when (val /= lFalse && not watched) $ do
            puebloWatch solver constr this t
          f ts
  f (puebloTerms this)

{--------------------------------------------------------------------
  Restart strategy
--------------------------------------------------------------------}

data RestartStrategy = MiniSATRestarts | ArminRestarts | LubyRestarts
  deriving (Show, Eq, Ord)

mkRestartSeq :: RestartStrategy -> Int -> Double -> [Int]
mkRestartSeq MiniSATRestarts = miniSatRestartSeq
mkRestartSeq ArminRestarts   = arminRestartSeq
mkRestartSeq LubyRestarts    = lubyRestartSeq

miniSatRestartSeq :: Int -> Double -> [Int]
miniSatRestartSeq start inc = iterate (ceiling . (inc *) . fromIntegral) start

{-
miniSatRestartSeq :: Int -> Double -> [Int]
miniSatRestartSeq start inc = map round $ iterate (inc*) (fromIntegral start)
-}

arminRestartSeq :: Int -> Double -> [Int]
arminRestartSeq start inc = go (fromIntegral start) (fromIntegral start)
  where  
    go !inner !outer = round inner : go inner' outer'
      where
        (inner',outer') = 
          if inner >= outer
          then (fromIntegral start, outer * inc)
          else (inner * inc, outer)

lubyRestartSeq :: Int -> Double -> [Int]
lubyRestartSeq start inc = map (ceiling . (fromIntegral start *) . luby inc) [0..]

{-
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


-}
luby :: Double -> Integer -> Double
luby y x = go2 size1 sequ1 x
  where
    -- Find the finite subsequence that contains index 'x', and the
    -- size of that subsequence:
    (size1, sequ1) = go 1 0

    go :: Integer -> Integer -> (Integer, Integer)
    go size sequ
      | size < x+1 = go (2*size+1) (sequ+1)
      | otherwise  = (size, sequ)

    go2 :: Integer -> Integer -> Integer -> Double
    go2 size sequ x2
      | size-1 /= x2 = let size' = (size-1) `div` 2 in go2 size' (sequ - 1) (x2 `mod` size')
      | otherwise = y ^ sequ


{--------------------------------------------------------------------
  utility
--------------------------------------------------------------------}

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM p = go
  where
    go [] = return True
    go (x:xs) = do
      b <- p x
      if b
        then go xs
        else return False

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM p = go
  where
    go [] = return False
    go (x:xs) = do
      b <- p x
      if b
        then return True
        else go xs

#if !MIN_VERSION_base(4,6,0)

modifyIORef' :: IORef a -> (a -> a) -> IO ()
modifyIORef' ref f = do
  x <- readIORef ref
  writeIORef ref $! f x

#endif

shift :: IORef [a] -> IO a
shift ref = do
  (x:xs) <- readIORef ref
  writeIORef ref xs
  return x

defaultHashWithSalt :: Hashable a => Int -> a -> Int
defaultHashWithSalt salt x = salt `combine` hash x
#if MIN_VERSION_hashable(1,2,0)
  where
    combine :: Int -> Int -> Int
    combine h1 h2 = (h1 * 16777619) `xor` h2
#endif

{--------------------------------------------------------------------
  debug
--------------------------------------------------------------------}

debugMode :: Bool
debugMode = False

checkSatisfied :: Solver -> IO ()
checkSatisfied solver = do
  cls <- readIORef (svConstrDB solver)
  forM_ cls $ \c -> do
    b <- isSatisfied solver c
    unless b $ do
      s <- showConstraintHandler solver c
      log solver $ "BUG: " ++ s ++ " is violated"

sanityCheck :: Solver -> IO ()
sanityCheck _ | not debugMode = return ()
sanityCheck solver = do
  cls <- readIORef (svConstrDB solver)
  forM_ cls $ \constr -> do
    lits <- watchedLiterals solver constr
    forM_ lits $ \l -> do
      ws <- watches solver l
      unless (constr `elem` ws) $ error $ printf "sanityCheck:A:%s" (show lits)

  vs <- variables solver
  let lits = [l | v <- vs, l <- [literal v True, literal v False]]
  forM_ lits $ \l -> do
    cs <- watches solver l
    forM_ cs $ \constr -> do
      lits2 <- watchedLiterals solver constr
      unless (l `elem` lits2) $ do
        error $ printf "sanityCheck:C:%d %s" l (show lits2)

dumpVarActivity :: Solver -> IO ()
dumpVarActivity solver = do
  log solver "Variable activity:"
  vs <- variables solver
  forM_ vs $ \v -> do
    activity <- varActivity solver v
    log solver $ printf "activity(%d) = %d" v activity

dumpConstrActivity :: Solver -> IO ()
dumpConstrActivity solver = do
  log solver "Learnt constraints activity:"
  xs <- learntConstraints solver
  forM_ xs $ \c -> do
    s <- showConstraintHandler solver c
    aval <- constrReadActivity c
    log solver $ printf "activity(%s) = %f" s aval

-- | set callback function for receiving messages.
setLogger :: Solver -> (String -> IO ()) -> IO ()
setLogger solver logger = do
  writeIORef (svLogger solver) (Just logger)

log :: Solver -> String -> IO ()
log solver msg = logIO solver (return msg)

logIO :: Solver -> IO String -> IO ()
logIO solver action = do
  m <- readIORef (svLogger solver)
  case m of
    Nothing -> return ()
    Just logger -> action >>= logger
