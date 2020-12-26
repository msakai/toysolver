{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
#ifdef __GLASGOW_HASKELL__
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
#endif
#include "MachDeps.h"
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Solver.CDCL
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
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
module ToySolver.SAT.Solver.CDCL
  (
  -- * The @Solver@ type
    Solver
  , newSolver
  , newSolverWithConfig

  -- * Basic data structures
  , Var
  , Lit
  , literal
  , litNot
  , litVar
  , litPolarity
  , evalLit

  -- * Problem specification
  , newVar
  , newVars
  , newVars_
  , resizeVarCapacity
  -- ** Clauses
  , AddClause (..)
  , Clause
  , evalClause
  , PackedClause
  , packClause
  , unpackClause
  -- ** Cardinality constraints
  , AddCardinality (..)
  , AtLeast
  , Exactly
  , evalAtLeast
  , evalExactly

  -- ** (Linear) pseudo-boolean constraints
  , AddPBLin (..)
  , PBLinTerm
  , PBLinSum
  , PBLinAtLeast
  , PBLinExactly
  , evalPBLinSum
  , evalPBLinAtLeast
  , evalPBLinExactly
  -- ** XOR clauses
  , AddXORClause (..)
  , XORClause
  , evalXORClause
  -- ** Theory
  , setTheory

  -- * Solving
  , solve
  , solveWith
  , BudgetExceeded (..)
  , cancel
  , Canceled (..)

  -- * Extract results
  , IModel (..)
  , Model
  , getModel
  , getFailedAssumptions
  , getAssumptionsImplications

  -- * Solver configulation
  , module ToySolver.SAT.Solver.CDCL.Config
  , getConfig
  , setConfig
  , modifyConfig
  , setVarPolarity
  , setLogger
  , setRandomGen
  , getRandomGen
  , setConfBudget

  -- * Read state
  , getNVars
  , getNConstraints
  , getNLearntConstraints
  , getVarFixed
  , getLitFixed
  , getFixedLiterals

  -- * Internal API
  , varBumpActivity
  , varDecayActivity
  ) where

import Prelude hiding (log)
import Control.Loop
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Control.Exception
import Data.Array.IO
import Data.Array.Unsafe (unsafeFreeze)
import Data.Array.Base (unsafeRead, unsafeWrite)
import Data.Bits (xor) -- for defining 'combine' function
import Data.Coerce
import Data.Default.Class
import Data.Either
import Data.Function (on)
import Data.Hashable
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.IORef
import Data.Int
import Data.List
import Data.Maybe
import Data.Ord
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Set as Set
import ToySolver.Internal.Data.IOURef
import qualified ToySolver.Internal.Data.IndexedPriorityQueue as PQ
import qualified ToySolver.Internal.Data.Vec as Vec
import Data.Typeable
import System.Clock
import qualified System.Random.MWC as Rand
import Text.Printf

#ifdef __GLASGOW_HASKELL__
import GHC.Types (IO (..))
import GHC.Exts hiding (Constraint)
#endif

import ToySolver.Data.LBool
import ToySolver.SAT.Solver.CDCL.Config
import ToySolver.SAT.Types
import ToySolver.SAT.TheorySolver
import ToySolver.Internal.Util (revMapM)

{--------------------------------------------------------------------
  LitArray
--------------------------------------------------------------------}

newtype LitArray = LitArray (IOUArray Int PackedLit) deriving (Eq)

newLitArray :: [Lit] -> IO LitArray
newLitArray lits = do
  let size = length lits
  liftM LitArray $ newListArray (0, size-1) (map packLit lits)

readLitArray :: LitArray -> Int -> IO Lit
readLitArray (LitArray a) i = liftM unpackLit $ unsafeRead a i
-- readLitArray (LitArray a) i = liftM unpackLit $ readArray a i

writeLitArray :: LitArray -> Int -> Lit -> IO ()
writeLitArray (LitArray a) i lit = unsafeWrite a i (packLit lit)
-- writeLitArray (LitArray a) i lit = writeArray a i (packLit lit)

getLits :: LitArray -> IO [Lit]
getLits (LitArray a) = liftM (map unpackLit) $ getElems a

getLitArraySize :: LitArray -> IO Int
getLitArraySize (LitArray a) = do
  (lb,ub) <- getBounds a
  assert (lb == 0) $ return ()
  return $! ub-lb+1

{--------------------------------------------------------------------
  internal data structures
--------------------------------------------------------------------}

type Level = Int

levelRoot :: Level
levelRoot = 0

litIndex :: Lit -> Int
litIndex l = 2 * (litVar l - 1) + (if litPolarity l then 1 else 0)

{-# INLINE varValue #-}
varValue :: Solver -> Var -> IO LBool
varValue solver v = liftM coerce $ Vec.unsafeRead (svVarValue solver) (v - 1)

{-# INLINE litValue #-}
litValue :: Solver -> Lit -> IO LBool
litValue solver !l = do
  -- litVar による heap allocation を避けるために、
  -- litPolarityによる分岐後にvarValueを呼ぶ。
  if litPolarity l then
    varValue solver l
  else do
    m <- varValue solver (negate l)
    return $! lnot m

getVarFixed :: Solver -> Var -> IO LBool
getVarFixed solver !v = do
  lv <- Vec.unsafeRead (svVarLevel solver) (v - 1)
  if lv == levelRoot then
    varValue solver v
  else
    return lUndef

getLitFixed :: Solver -> Lit -> IO LBool
getLitFixed solver !l = do
  -- litVar による heap allocation を避けるために、
  -- litPolarityによる分岐後にvarGetFixedを呼ぶ。
  if litPolarity l then
    getVarFixed solver l
  else do
    m <- getVarFixed solver (negate l)
    return $! lnot m

getNFixed :: Solver -> IO Int
getNFixed solver = do
  lv <- getDecisionLevel solver
  if lv == levelRoot then
    Vec.getSize (svTrail solver)
  else
    Vec.unsafeRead (svTrailLimit solver) 0

-- | it returns a set of literals that are fixed without any assumptions.
getFixedLiterals :: Solver -> IO [Lit]
getFixedLiterals solver = do
  n <- getNFixed solver
  revMapM (Vec.unsafeRead (svTrail solver)) [0..n-1]

varLevel :: Solver -> Var -> IO Level
varLevel solver !v = do
  val <- varValue solver v
  when (val == lUndef) $ error ("ToySolver.SAT.varLevel: unassigned var " ++ show v)
  Vec.unsafeRead (svVarLevel solver) (v - 1)

litLevel :: Solver -> Lit -> IO Level
litLevel solver l = varLevel solver (litVar l)

varReason :: Solver -> Var -> IO (Maybe SomeConstraintHandler)
varReason solver !v = do
  val <- varValue solver v
  when (val == lUndef) $ error ("ToySolver.SAT.varReason: unassigned var " ++ show v)
  Vec.unsafeRead (svVarReason solver) (v - 1)

varAssignNo :: Solver -> Var -> IO Int
varAssignNo solver !v = do
  val <- varValue solver v
  when (val == lUndef) $ error ("ToySolver.SAT.varAssignNo: unassigned var " ++ show v)
  Vec.unsafeRead (svVarTrailIndex solver) (v - 1)

-- | Solver instance
data Solver
  = Solver
  { svOk           :: !(IORef Bool)

  , svVarQueue     :: !PQ.PriorityQueue
  , svTrail        :: !(Vec.UVec Lit)
  , svTrailLimit   :: !(Vec.UVec Lit)
  , svTrailNPropagated :: !(IOURef Int)

  -- variable information
  , svVarValue      :: !(Vec.UVec Int8) -- should be 'Vec.UVec LBool' but it's difficult to define MArray instance
  , svVarPolarity   :: !(Vec.UVec Bool)
  , svVarActivity   :: !(Vec.UVec VarActivity)
  , svVarTrailIndex :: !(Vec.UVec Int)
  , svVarLevel      :: !(Vec.UVec Int)
  -- | will be invoked once when the variable is assigned
  , svVarWatches      :: !(Vec.Vec [SomeConstraintHandler])
  , svVarOnUnassigned :: !(Vec.Vec [SomeConstraintHandler])
  , svVarReason       :: !(Vec.Vec (Maybe SomeConstraintHandler))
  -- | exponential moving average estimate
  , svVarEMAScaled    :: !(Vec.UVec Double)
  -- | When v was last assigned
  , svVarWhenAssigned :: !(Vec.UVec Int)
  -- | The number of learnt clauses v participated in generating since Assigned.
  , svVarParticipated :: !(Vec.UVec Int)
  -- | The number of learnt clauses v reasoned in generating since Assigned.
  , svVarReasoned     :: !(Vec.UVec Int)

  -- | will be invoked when this literal is falsified
  , svLitWatches   :: !(Vec.Vec [SomeConstraintHandler])
  , svLitOccurList :: !(Vec.Vec (HashSet SomeConstraintHandler))

  , svConstrDB     :: !(IORef [SomeConstraintHandler])
  , svLearntDB     :: !(IORef (Int,[SomeConstraintHandler]))

  -- Theory
  , svTheorySolver  :: !(IORef (Maybe TheorySolver))
  , svTheoryChecked :: !(IOURef Int)

  -- Result
  , svModel        :: !(IORef (Maybe Model))
  , svFailedAssumptions :: !(IORef [Lit])
  , svAssumptionsImplications :: !(IORef LitSet)

  -- Statistics
  , svNDecision    :: !(IOURef Int)
  , svNRandomDecision :: !(IOURef Int)
  , svNConflict    :: !(IOURef Int)
  , svNRestart     :: !(IOURef Int)
  , svNLearntGC    :: !(IOURef Int)
  , svNRemovedConstr :: !(IOURef Int)

  -- Configulation
  , svConfig :: !(IORef Config)
  , svRandomGen  :: !(IORef Rand.GenIO)
  , svConfBudget :: !(IOURef Int)

  -- Logging
  , svLogger :: !(IORef (Maybe (String -> IO ())))
  , svStartWC    :: !(IORef TimeSpec)
  , svLastStatWC :: !(IORef TimeSpec)

  -- Working spaces
  , svCanceled        :: !(IORef Bool)
  , svAssumptions     :: !(Vec.UVec Lit)
  , svLearntLim       :: !(IORef Int)
  , svLearntLimAdjCnt :: !(IORef Int)
  , svLearntLimSeq    :: !(IORef [(Int,Int)])
  , svSeen :: !(Vec.UVec Bool)
  , svPBLearnt :: !(IORef (Maybe PBLinAtLeast))

  -- | Amount to bump next variable with.
  , svVarInc       :: !(IOURef Double)

  -- | Amount to bump next constraint with.
  , svConstrInc    :: !(IOURef Double)

  -- ERWA / LRB

  -- | step-size parameter α
  , svERWAStepSize :: !(IOURef Double)
  , svEMAScale :: !(IOURef Double)
  , svLearntCounter :: !(IOURef Int)
  }

markBad :: Solver -> IO ()
markBad solver = do
  writeIORef (svOk solver) False
  bcpClear solver

bcpDequeue :: Solver -> IO (Maybe Lit)
bcpDequeue solver = do
  n <- Vec.getSize (svTrail solver)
  m <- readIOURef (svTrailNPropagated solver)
  if m==n then
    return Nothing
  else do
    -- m < n
    lit <- Vec.unsafeRead (svTrail solver) m
    modifyIOURef (svTrailNPropagated solver) (+1)
    return (Just lit)

bcpIsEmpty :: Solver -> IO Bool
bcpIsEmpty solver = do
  p <- readIOURef (svTrailNPropagated solver)
  n <- Vec.getSize (svTrail solver)
  return $! n == p

bcpCheckEmpty :: Solver -> IO ()
bcpCheckEmpty solver = do
  empty <- bcpIsEmpty solver
  unless empty $
    error "BUG: BCP Queue should be empty at this point"

bcpClear :: Solver -> IO ()
bcpClear solver = do
  m <- Vec.getSize (svTrail solver)
  writeIOURef (svTrailNPropagated solver) m

assignBy :: Solver -> Lit -> SomeConstraintHandler -> IO Bool
assignBy solver lit c = do
  lv <- getDecisionLevel solver
  let !c2 = if lv == levelRoot
            then Nothing
            else Just c
  assign_ solver lit c2

assign :: Solver -> Lit -> IO Bool
assign solver lit = assign_ solver lit Nothing

assign_ :: Solver -> Lit -> Maybe SomeConstraintHandler -> IO Bool
assign_ solver !lit reason = assert (validLit lit) $ do
  let val = liftBool (litPolarity lit)

  val0 <- varValue solver (litVar lit)
  if val0 /= lUndef then do
    return $ val == val0
  else do
    idx <- Vec.getSize (svTrail solver)
    lv <- getDecisionLevel solver

    Vec.unsafeWrite (svVarValue solver) (litVar lit - 1) (coerce val)
    Vec.unsafeWrite (svVarTrailIndex solver) (litVar lit - 1) idx
    Vec.unsafeWrite (svVarLevel solver) (litVar lit - 1) lv
    Vec.unsafeWrite (svVarReason solver) (litVar lit - 1) reason
    Vec.unsafeWrite (svVarWhenAssigned solver) (litVar lit - 1) =<< readIOURef (svLearntCounter solver)
    Vec.unsafeWrite (svVarParticipated solver) (litVar lit - 1) 0
    Vec.unsafeWrite (svVarReasoned solver) (litVar lit - 1) 0

    Vec.push (svTrail solver) lit

    when debugMode $ logIO solver $ do
      let r = case reason of
                Nothing -> ""
                Just _ -> " by propagation"
      return $ printf "assign(level=%d): %d%s" lv lit r

    return True

unassign :: Solver -> Var -> IO ()
unassign solver !v = assert (validVar v) $ do
  val <- varValue solver v
  when (val == lUndef) $ error "unassign: should not happen"

  flag <- configEnablePhaseSaving <$> getConfig solver
  when flag $ Vec.unsafeWrite (svVarPolarity solver) (v - 1) $! fromJust (unliftBool val)

  Vec.unsafeWrite (svVarValue solver) (v - 1) (coerce lUndef)
  Vec.unsafeWrite (svVarTrailIndex solver) (v - 1) maxBound
  Vec.unsafeWrite (svVarLevel solver) (v - 1) maxBound
  Vec.unsafeWrite (svVarReason solver) (v - 1) Nothing

  -- ERWA / LRB computation
  interval <- do
    t2 <- readIOURef (svLearntCounter solver)
    t1 <- Vec.unsafeRead (svVarWhenAssigned solver) (v - 1)
    return (t2 - t1)
  -- Interval = 0 is possible due to restarts.
  when (interval > 0) $ do
    participated <- Vec.unsafeRead (svVarParticipated solver) (v - 1)
    reasoned <- Vec.unsafeRead (svVarReasoned solver) (v - 1)
    alpha <- readIOURef (svERWAStepSize solver)
    let learningRate = fromIntegral participated / fromIntegral interval
        reasonSideRate = fromIntegral reasoned / fromIntegral interval
    scale <- readIOURef (svEMAScale solver)
    -- ema := (1 - α)ema + α*r
    Vec.unsafeModify (svVarEMAScaled solver) (v - 1) (\orig -> (1 - alpha) * orig + alpha * scale * (learningRate + reasonSideRate))
    -- If v is assigned by random decision, it's possible that v is still in the queue.
    PQ.update (svVarQueue solver) v

  let !l = if val == lTrue then v else -v
  cs <- Vec.unsafeRead (svVarOnUnassigned solver) (v - 1)
  Vec.unsafeWrite (svVarOnUnassigned solver) (v - 1) []
  forM_ cs $ \c ->
    constrOnUnassigned solver c c l

  PQ.enqueue (svVarQueue solver) v

addOnUnassigned :: Solver -> SomeConstraintHandler -> Lit -> IO ()
addOnUnassigned solver constr !l = do
  val <- varValue solver (litVar l)
  when (val == lUndef) $ error "addOnUnassigned: should not happen"
  Vec.unsafeModify (svVarOnUnassigned solver) (litVar l - 1) (constr :)

-- | Register the constraint to be notified when the literal becames false.
watchLit :: Solver -> Lit -> SomeConstraintHandler -> IO ()
watchLit solver !lit c = Vec.unsafeModify (svLitWatches solver) (litIndex lit) (c : )

-- | Register the constraint to be notified when the variable is assigned.
watchVar :: Solver -> Var -> SomeConstraintHandler -> IO ()
watchVar solver !var c = Vec.unsafeModify (svVarWatches solver) (var - 1) (c :)

unwatchLit :: Solver -> Lit -> SomeConstraintHandler -> IO ()
unwatchLit solver !lit c = Vec.unsafeModify (svLitWatches solver) (litIndex lit) (delete c)

unwatchVar :: Solver -> Lit -> SomeConstraintHandler -> IO ()
unwatchVar solver !var c = Vec.unsafeModify (svVarWatches solver) (var - 1) (delete c)

addToDB :: ConstraintHandler c => Solver -> c -> IO ()
addToDB solver c = do
  let c2 = toConstraintHandler c
  modifyIORef (svConstrDB solver) (c2 : )
  when debugMode $ logIO solver $ do
    str <- showConstraintHandler c
    return $ printf "constraint %s is added" str

  b <- isPBRepresentable c
  when b $ do
    (lhs,_) <- toPBLinAtLeast c
    forM_ lhs $ \(_,lit) -> do
       Vec.unsafeModify (svLitOccurList solver) (litIndex lit) (HashSet.insert c2)

addToLearntDB :: ConstraintHandler c => Solver -> c -> IO ()
addToLearntDB solver c = do
  modifyIORef (svLearntDB solver) $ \(n,xs) -> (n+1, toConstraintHandler c : xs)
  when debugMode $ logIO solver $ do
    str <- showConstraintHandler c
    return $ printf "constraint %s is added" str

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
varActivity solver v = Vec.unsafeRead (svVarActivity solver) (v - 1)

varDecayActivity :: Solver -> IO ()
varDecayActivity solver = do
  d <- configVarDecay <$> getConfig solver
  modifyIOURef (svVarInc solver) (d*)

varBumpActivity :: Solver -> Var -> IO ()
varBumpActivity solver !v = do
  inc <- readIOURef (svVarInc solver)
  Vec.unsafeModify (svVarActivity solver) (v - 1) (+inc)
  conf <- getConfig solver
  when (configBranchingStrategy conf == BranchingVSIDS) $ do
    PQ.update (svVarQueue solver) v
  aval <- Vec.unsafeRead (svVarActivity solver) (v - 1)
  when (aval > 1e20) $
    -- Rescale
    varRescaleAllActivity solver

varRescaleAllActivity :: Solver -> IO ()
varRescaleAllActivity solver = do
  let a = svVarActivity solver
  n <- getNVars solver
  forLoop 0 (<n) (+1) $ \i ->
    Vec.unsafeModify a i (* 1e-20)
  modifyIOURef (svVarInc solver) (* 1e-20)

varEMAScaled :: Solver -> Var -> IO Double
varEMAScaled solver v = Vec.unsafeRead (svVarEMAScaled solver) (v - 1)

varIncrementParticipated :: Solver -> Var -> IO ()
varIncrementParticipated solver v = Vec.unsafeModify (svVarParticipated solver) (v - 1) (+1)

varIncrementReasoned :: Solver -> Var -> IO ()
varIncrementReasoned solver v = Vec.unsafeModify (svVarReasoned solver) (v - 1) (+1)

varEMADecay :: Solver -> IO ()
varEMADecay solver = do
  config <- getConfig solver

  alpha <- readIOURef (svERWAStepSize solver)
  let alphaMin = configERWAStepSizeMin config
  when (alpha > alphaMin) $ do
    writeIOURef (svERWAStepSize solver) (max alphaMin (alpha - configERWAStepSizeDec config))

  case configBranchingStrategy config of
    BranchingLRB -> do
      modifyIOURef (svEMAScale solver) (configEMADecay config *)
      scale <- readIOURef (svEMAScale solver)
      when (scale > 1e20) $ do
        n <- getNVars solver
        let a = svVarEMAScaled solver
        forLoop 0 (<n) (+1) $ \i -> Vec.unsafeModify a i (/ scale)
        writeIOURef (svEMAScale solver) 1.0
    _ -> return ()

variables :: Solver -> IO [Var]
variables solver = do
  n <- getNVars solver
  return [1 .. n]

-- | number of variables of the problem.
getNVars :: Solver -> IO Int
getNVars solver = Vec.getSize (svVarValue solver)

-- | number of assigned
getNAssigned :: Solver -> IO Int
getNAssigned solver = Vec.getSize (svTrail solver)

-- | number of constraints.
getNConstraints :: Solver -> IO Int
getNConstraints solver = do
  xs <- readIORef (svConstrDB solver)
  return $ length xs

-- | number of learnt constrints.
getNLearntConstraints :: Solver -> IO Int
getNLearntConstraints solver = do
  (n,_) <- readIORef (svLearntDB solver)
  return n

learntConstraints :: Solver -> IO [SomeConstraintHandler]
learntConstraints solver = do
  (_,cs) <- readIORef (svLearntDB solver)
  return cs

{--------------------------------------------------------------------
  Solver
--------------------------------------------------------------------}

-- | Create a new 'Solver' instance.
newSolver :: IO Solver
newSolver = newSolverWithConfig def

-- | Create a new 'Solver' instance with a given configulation.
newSolverWithConfig :: Config -> IO Solver
newSolverWithConfig config = do
 rec
  ok   <- newIORef True
  trail <- Vec.new
  trail_lim <- Vec.new
  trail_nprop <- newIOURef 0

  varValue <- Vec.new
  varPolarity <- Vec.new
  varActivity <- Vec.new
  varTrailIndex <- Vec.new
  varLevel <- Vec.new
  varWatches <- Vec.new
  varOnUnassigned <- Vec.new
  varReason <- Vec.new
  varEMAScaled <- Vec.new
  varWhenAssigned <- Vec.new
  varParticipated <- Vec.new
  varReasoned <- Vec.new
  litWatches <- Vec.new
  litOccurList <- Vec.new

  vqueue <- PQ.newPriorityQueueBy (ltVar solver)
  db  <- newIORef []
  db2 <- newIORef (0,[])
  as  <- Vec.new
  m   <- newIORef Nothing
  canceled <- newIORef False
  ndecision <- newIOURef 0
  nranddec  <- newIOURef 0
  nconflict <- newIOURef 0
  nrestart  <- newIOURef 0
  nlearntgc <- newIOURef 0
  nremoved  <- newIOURef 0

  constrInc   <- newIOURef 1
  varInc   <- newIOURef 1

  configRef <- newIORef config

  learntLim       <- newIORef undefined
  learntLimAdjCnt <- newIORef (-1)
  learntLimSeq    <- newIORef undefined

  logger <- newIORef Nothing
  startWC    <- newIORef undefined
  lastStatWC <- newIORef undefined

  randgen  <- newIORef =<< Rand.create

  failed <- newIORef []
  implied <- newIORef IS.empty

  confBudget <- newIOURef (-1)

  tsolver <- newIORef Nothing
  tchecked <- newIOURef 0

  seen <- Vec.new
  pbLearnt <- newIORef Nothing

  alpha <- newIOURef 0.4
  emaScale <- newIOURef 1.0
  learntCounter <- newIOURef 0

  let solver =
        Solver
        { svOk = ok
        , svVarQueue   = vqueue
        , svTrail      = trail
        , svTrailLimit = trail_lim
        , svTrailNPropagated = trail_nprop

        , svVarValue        = varValue
        , svVarPolarity     = varPolarity
        , svVarActivity     = varActivity
        , svVarTrailIndex   = varTrailIndex
        , svVarLevel        = varLevel
        , svVarWatches      = varWatches
        , svVarOnUnassigned = varOnUnassigned
        , svVarReason       = varReason
        , svVarEMAScaled    = varEMAScaled
        , svVarWhenAssigned = varWhenAssigned
        , svVarParticipated = varParticipated
        , svVarReasoned     = varReasoned
        , svLitWatches      = litWatches
        , svLitOccurList    = litOccurList

        , svConstrDB   = db
        , svLearntDB   = db2

        -- Theory
        , svTheorySolver  = tsolver
        , svTheoryChecked = tchecked

        -- Result
        , svModel      = m
        , svFailedAssumptions = failed
        , svAssumptionsImplications = implied

        -- Statistics
        , svNDecision  = ndecision
        , svNRandomDecision = nranddec
        , svNConflict  = nconflict
        , svNRestart   = nrestart
        , svNLearntGC  = nlearntgc
        , svNRemovedConstr = nremoved

        -- Configulation
        , svConfig     = configRef
        , svRandomGen  = randgen
        , svConfBudget = confBudget

        -- Logging
        , svLogger = logger
        , svStartWC    = startWC
        , svLastStatWC = lastStatWC

        -- Working space
        , svCanceled        = canceled
        , svAssumptions     = as
        , svLearntLim       = learntLim
        , svLearntLimAdjCnt = learntLimAdjCnt
        , svLearntLimSeq    = learntLimSeq
        , svVarInc      = varInc
        , svConstrInc   = constrInc
        , svSeen = seen
        , svPBLearnt = pbLearnt

        , svERWAStepSize = alpha
        , svEMAScale = emaScale
        , svLearntCounter = learntCounter
        }
 return solver

ltVar :: Solver -> Var -> Var -> IO Bool
ltVar solver !v1 !v2 = do
  conf <- getConfig solver
  case configBranchingStrategy conf of
    BranchingVSIDS -> do
      a1 <- varActivity solver v1
      a2 <- varActivity solver v2
      return $! a1 > a2
    _ -> do -- BranchingERWA and BranchingLRB
      a1 <- varEMAScaled solver v1
      a2 <- varEMAScaled solver v1
      return $! a1 > a2

{--------------------------------------------------------------------
  Problem specification
--------------------------------------------------------------------}

instance NewVar IO Solver where
  newVar :: Solver -> IO Var
  newVar solver = do
    n <- Vec.getSize (svVarValue solver)
#if SIZEOF_HSINT > 4
    when (n == fromIntegral (maxBound :: PackedLit)) $ do
      error "cannot allocate more variables"
#endif
    let v = n + 1

    Vec.push (svVarValue solver) (coerce lUndef)
    Vec.push (svVarPolarity solver) True
    Vec.push (svVarActivity solver) 0
    Vec.push (svVarTrailIndex solver) maxBound
    Vec.push (svVarLevel solver) maxBound
    Vec.push (svVarWatches solver) []
    Vec.push (svVarOnUnassigned solver) []
    Vec.push (svVarReason solver) Nothing
    Vec.push (svVarEMAScaled solver) 0
    Vec.push (svVarWhenAssigned solver) (-1)
    Vec.push (svVarParticipated solver) 0
    Vec.push (svVarReasoned solver) 0

    Vec.push (svLitWatches solver) []
    Vec.push (svLitWatches solver) []
    Vec.push (svLitOccurList solver) HashSet.empty
    Vec.push (svLitOccurList solver) HashSet.empty

    PQ.enqueue (svVarQueue solver) v
    Vec.push (svSeen solver) False
    return v

  newVars :: Solver -> Int -> IO [Var]
  newVars solver n = do
    nv <- getNVars solver
#if SIZEOF_HSINT > 4
    when (nv + n > fromIntegral (maxBound :: PackedLit)) $ do
      error "cannot allocate more variables"
#endif
    resizeVarCapacity solver (nv+n)
    replicateM n (newVar solver)

  newVars_ :: Solver -> Int -> IO ()
  newVars_ solver n = do
    nv <- getNVars solver
#if SIZEOF_HSINT > 4
    when (nv + n > fromIntegral (maxBound :: PackedLit)) $ do
      error "cannot allocate more variables"
#endif
    resizeVarCapacity solver (nv+n)
    replicateM_ n (newVar solver)

-- |Pre-allocate internal buffer for @n@ variables.
resizeVarCapacity :: Solver -> Int -> IO ()
resizeVarCapacity solver n = do
  Vec.resizeCapacity (svVarValue solver) n
  Vec.resizeCapacity (svVarPolarity solver) n
  Vec.resizeCapacity (svVarActivity solver) n
  Vec.resizeCapacity (svVarTrailIndex solver) n
  Vec.resizeCapacity (svVarLevel solver) n
  Vec.resizeCapacity (svVarWatches solver) n
  Vec.resizeCapacity (svVarOnUnassigned solver) n
  Vec.resizeCapacity (svVarReason solver) n
  Vec.resizeCapacity (svVarEMAScaled solver) n
  Vec.resizeCapacity (svVarWhenAssigned solver) n
  Vec.resizeCapacity (svVarParticipated solver) n
  Vec.resizeCapacity (svVarReasoned solver) n
  Vec.resizeCapacity (svLitWatches solver) (n*2)
  Vec.resizeCapacity (svLitOccurList solver) (n*2)
  Vec.resizeCapacity (svSeen solver) n
  PQ.resizeHeapCapacity (svVarQueue solver) n
  PQ.resizeTableCapacity (svVarQueue solver) (n+1)

instance AddClause IO Solver where
  addClause :: Solver -> Clause -> IO ()
  addClause solver lits = do
    d <- getDecisionLevel solver
    assert (d == levelRoot) $ return ()

    ok <- readIORef (svOk solver)
    when ok $ do
      m <- instantiateClause (getLitFixed solver) lits
      case normalizeClause =<< m of
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
        Just lits2 -> do
          subsumed <- checkForwardSubsumption solver lits
          unless subsumed $ do
            removeBackwardSubsumedBy solver ([(1,lit) | lit <- lits2], 1)
            clause <- newClauseHandler lits2 False
            addToDB solver clause
            _ <- basicAttachClauseHandler solver clause
            return ()

instance AddCardinality IO Solver where
  addAtLeast :: Solver -> [Lit] -> Int -> IO ()
  addAtLeast solver lits n = do
    d <- getDecisionLevel solver
    assert (d == levelRoot) $ return ()

    ok <- readIORef (svOk solver)
    when ok $ do
      (lits',n') <- liftM normalizeAtLeast $ instantiateAtLeast (getLitFixed solver) (lits,n)
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
      else do -- n' < len
        removeBackwardSubsumedBy solver ([(1,lit) | lit <- lits'], fromIntegral n')
        c <- newAtLeastHandler lits' n' False
        addToDB solver c
        _ <- basicAttachAtLeastHandler solver c
        return ()

instance AddPBLin IO Solver where
  addPBAtLeast :: Solver -> PBLinSum -> Integer -> IO ()
  addPBAtLeast solver ts n = do
    d <- getDecisionLevel solver
    assert (d == levelRoot) $ return ()

    ok <- readIORef (svOk solver)
    when ok $ do
      (ts',n') <- liftM normalizePBLinAtLeast $ instantiatePBLinAtLeast (getLitFixed solver) (ts,n)

      case pbToAtLeast (ts',n') of
        Just (lhs',rhs') -> addAtLeast solver lhs' rhs'
        Nothing -> do
          let cs = map fst ts'
              slack = sum cs - n'
          if n' <= 0 then return ()
          else if slack < 0 then markBad solver
          else do
            removeBackwardSubsumedBy solver (ts', n')
            (ts'',n'') <- do
              b <- configEnablePBSplitClausePart <$> getConfig solver
              if b
              then pbSplitClausePart solver (ts',n')
              else return (ts',n')

            c <- newPBHandler solver ts'' n'' False
            let constr = toConstraintHandler c
            addToDB solver constr
            ret <- attach solver constr
            if not ret then do
              markBad solver
            else do
              ret2 <- deduce solver
              case ret2 of
                Nothing -> return ()
                Just _ -> markBad solver

  addPBExactly :: Solver -> PBLinSum -> Integer -> IO ()
  addPBExactly solver ts n = do
    (ts2,n2) <- liftM normalizePBLinExactly $ instantiatePBLinExactly (getLitFixed solver) (ts,n)
    addPBAtLeast solver ts2 n2
    addPBAtMost solver ts2 n2

  addPBAtLeastSoft :: Solver -> Lit -> PBLinSum -> Integer -> IO ()
  addPBAtLeastSoft solver sel lhs rhs = do
    (lhs', rhs') <- liftM normalizePBLinAtLeast $ instantiatePBLinAtLeast (getLitFixed solver) (lhs,rhs)
    addPBAtLeast solver ((rhs', litNot sel) : lhs') rhs'

  addPBExactlySoft :: Solver -> Lit -> PBLinSum -> Integer -> IO ()
  addPBExactlySoft solver sel lhs rhs = do
    (lhs2, rhs2) <- liftM normalizePBLinExactly $ instantiatePBLinExactly (getLitFixed solver) (lhs,rhs)
    addPBAtLeastSoft solver sel lhs2 rhs2
    addPBAtMostSoft solver sel lhs2 rhs2

-- | See documentation of 'setPBSplitClausePart'.
pbSplitClausePart :: Solver -> PBLinAtLeast -> IO PBLinAtLeast
pbSplitClausePart solver (lhs,rhs) = do
  let (ts1,ts2) = partition (\(c,_) -> c >= rhs) lhs
  if length ts1 < 2 then
    return (lhs,rhs)
  else do
    sel <- newVar solver
    addClause solver $ -sel : [l | (_,l) <- ts1]
    return ((rhs,sel) : ts2, rhs)

instance AddXORClause IO Solver where
  addXORClause :: Solver -> [Lit] -> Bool -> IO ()
  addXORClause solver lits rhs = do
    d <- getDecisionLevel solver
    assert (d == levelRoot) $ return ()

    ok <- readIORef (svOk solver)
    when ok $ do
      xcl <- instantiateXORClause (getLitFixed solver) (lits,rhs)
      case normalizeXORClause xcl of
        ([], True) -> markBad solver
        ([], False) -> return ()
        ([l], b) -> addClause solver [if b then l else litNot l]
        (l:ls, b) -> do
          c <- newXORClauseHandler ((if b then l else litNot l) : ls) False
          addToDB solver c
          _ <- basicAttachXORClauseHandler solver c
          return ()

{--------------------------------------------------------------------
  Problem solving
--------------------------------------------------------------------}

-- | Solve constraints.
-- Returns 'True' if the problem is SATISFIABLE.
-- Returns 'False' if the problem is UNSATISFIABLE.
solve :: Solver -> IO Bool
solve solver = do
  Vec.clear (svAssumptions solver)
  solve_ solver

-- | Solve constraints under assuptions.
-- Returns 'True' if the problem is SATISFIABLE.
-- Returns 'False' if the problem is UNSATISFIABLE.
solveWith :: Solver
          -> [Lit]    -- ^ Assumptions
          -> IO Bool
solveWith solver ls = do
  Vec.clear (svAssumptions solver)
  mapM_ (Vec.push (svAssumptions solver)) ls
  solve_ solver

solve_ :: Solver -> IO Bool
solve_ solver = do
  config <- getConfig solver
  writeIORef (svAssumptionsImplications solver) IS.empty

  log solver "Solving starts ..."
  resetStat solver
  writeIORef (svCanceled solver) False
  writeIORef (svModel solver) Nothing
  writeIORef (svFailedAssumptions solver) []

  ok <- readIORef (svOk solver)
  if not ok then
    return False
  else do
    when debugMode $ dumpVarActivity solver
    d <- getDecisionLevel solver
    assert (d == levelRoot) $ return ()

    nv <- getNVars solver
    Vec.resizeCapacity (svTrail solver) nv

    unless (configRestartInc config > 1) $ error "RestartInc must be >1"
    let restartSeq =
          if configRestartFirst config  > 0
          then mkRestartSeq (configRestartStrategy config) (configRestartFirst config) (configRestartInc config)
          else repeat 0

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
      unless (configLearntSizeInc config > 1) $ error "LearntSizeInc must be >1"
      nc <- getNConstraints solver
      let initialLearntLim = if configLearntSizeFirst config > 0 then configLearntSizeFirst config else max ((nc + nv) `div` 3) 16
          learntSizeSeq    = iterate (ceiling . (configLearntSizeInc config *) . fromIntegral) initialLearntLim
          learntSizeAdjSeq = iterate (\x -> (x * 3) `div` 2) (100::Int)
      writeIORef (svLearntLimSeq solver) (zip learntSizeSeq learntSizeAdjSeq)
      learntSizeAdj

    unless (0 <= configERWAStepSizeFirst config && configERWAStepSizeFirst config <= 1) $
      error "ERWAStepSizeFirst must be in [0..1]"
    unless (0 <= configERWAStepSizeMin config && configERWAStepSizeFirst config <= 1) $
      error "ERWAStepSizeMin must be in [0..1]"
    unless (0 <= configERWAStepSizeDec config) $
      error "ERWAStepSizeDec must be >=0"
    writeIOURef (svERWAStepSize solver) (configERWAStepSizeFirst config)

    let loop [] = error "solve_: should not happen"
        loop (conflict_lim:rs) = do
          printStat solver True
          ret <- search solver conflict_lim onConflict
          case ret of
            SRFinished x -> return $ Right x
            SRBudgetExceeded -> return $ Left (throw BudgetExceeded)
            SRCanceled -> return $ Left (throw Canceled)
            SRRestart -> do
              modifyIOURef (svNRestart solver) (+1)
              backtrackTo solver levelRoot
              loop rs

    printStatHeader solver

    startCPU <- getTime ProcessCPUTime
    startWC  <- getTime Monotonic
    writeIORef (svStartWC solver) startWC
    result <- loop restartSeq
    endCPU <- getTime ProcessCPUTime
    endWC  <- getTime Monotonic

    case result of
      Right True -> do
        when (configCheckModel config) $ checkSatisfied solver
        constructModel solver
        mt <- getTheory solver
        case mt of
          Nothing -> return ()
          Just t -> thConstructModel t
      _ -> return ()
    case result of
      Right False -> return ()
      _ -> saveAssumptionsImplications solver

    backtrackTo solver levelRoot

    when debugMode $ dumpVarActivity solver
    when debugMode $ dumpConstrActivity solver
    printStat solver True
    let durationSecs :: TimeSpec -> TimeSpec -> Double
        durationSecs start end = fromIntegral (toNanoSecs (end `diffTimeSpec` start)) / 10^(9::Int)
    (log solver . printf "#cpu_time = %.3fs") (durationSecs startCPU endCPU)
    (log solver . printf "#wall_clock_time = %.3fs") (durationSecs startWC endWC)
    (log solver . printf "#decision = %d") =<< readIOURef (svNDecision solver)
    (log solver . printf "#random_decision = %d") =<< readIOURef (svNRandomDecision solver)
    (log solver . printf "#conflict = %d") =<< readIOURef (svNConflict solver)
    (log solver . printf "#restart = %d")  =<< readIOURef (svNRestart solver)

    case result of
      Right x  -> return x
      Left m -> m

data BudgetExceeded = BudgetExceeded
  deriving (Show, Typeable)

instance Exception BudgetExceeded

data Canceled = Canceled
  deriving (Show, Typeable)

instance Exception Canceled

data SearchResult
  = SRFinished Bool
  | SRRestart
  | SRBudgetExceeded
  | SRCanceled

search :: Solver -> Int -> IO () -> IO SearchResult
search solver !conflict_lim onConflict = do
  conflictCounter <- newIORef 0
  let
    loop :: IO SearchResult
    loop = do
      conflict <- deduce solver
      case conflict of
        Just constr -> do
          ret <- handleConflict conflictCounter constr
          case ret of
            Just sr -> return sr
            Nothing -> loop
        Nothing -> do
          lv <- getDecisionLevel solver
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
      n <- getNLearntConstraints solver
      m <- getNAssigned solver
      learnt_lim <- readIORef (svLearntLim solver)
      when (learnt_lim >= 0 && n - m > learnt_lim) $ do
        modifyIOURef (svNLearntGC solver) (+1)
        reduceDB solver

    pickAssumption :: IO (Maybe Lit)
    pickAssumption = do
      s <- Vec.getSize (svAssumptions solver)
      let go = do
              d <- getDecisionLevel solver
              if not (d < s) then
                return (Just litUndef)
              else do
                l <- Vec.unsafeRead (svAssumptions solver) d
                val <- litValue solver l
                if val == lTrue then do
                  -- dummy decision level
                  pushDecisionLevel solver
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
      varEMADecay solver
      varDecayActivity solver
      constrDecayActivity solver
      onConflict

      modifyIOURef (svNConflict solver) (+1)
      d <- getDecisionLevel solver

      when debugMode $ logIO solver $ do
        str <- showConstraintHandler constr
        return $ printf "conflict(level=%d): %s" d str

      modifyIORef' conflictCounter (+1)
      c <- readIORef conflictCounter

      modifyIOURef (svConfBudget solver) $ \confBudget ->
        if confBudget > 0 then confBudget - 1 else confBudget
      confBudget <- readIOURef (svConfBudget solver)
      canceled <- readIORef (svCanceled solver)

      when (c `mod` 100 == 0) $ do
        printStat solver False

      if d == levelRoot then do
        markBad solver
        return $ Just (SRFinished False)
      else if confBudget==0 then
        return $ Just SRBudgetExceeded
      else if canceled then
        return $ Just SRCanceled
      else if conflict_lim > 0 && c >= conflict_lim then
        return $ Just SRRestart
      else do
        modifyIOURef (svLearntCounter solver) (+1)
        config <- getConfig solver
        case configLearningStrategy config of
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
          let constr2 = toConstraintHandler cl
          addToLearntDB solver constr2
          basicAttachClauseHandler solver cl
          assignBy solver lit constr2
          constrBumpActivity solver constr2

    learnHybrid :: IORef Int -> SomeConstraintHandler -> IO (Maybe SearchResult)
    learnHybrid conflictCounter constr = do
      (learntClause, clauseLevel) <- analyzeConflict solver constr
      (pb, minLevel) <- do
        z <- readIORef (svPBLearnt solver)
        case z of
          Nothing -> return (z, clauseLevel)
          Just pb -> do
            pbLevel <- pbBacktrackLevel solver pb
            return (z, min clauseLevel pbLevel)
      backtrackTo solver minLevel

      case learntClause of
        [] -> error "search(LearningHybrid): should not happen"
        [lit] -> do
          _ <- assign solver lit -- This should always succeed.
          return ()
        lit:_ -> do
          cl <- newClauseHandler learntClause True
          let constr2 = toConstraintHandler cl
          addToLearntDB solver constr2
          basicAttachClauseHandler solver cl
          constrBumpActivity solver constr2
          when (minLevel == clauseLevel) $ do
            _ <- assignBy solver lit constr2 -- This should always succeed.
            return ()

      ret <- deduce solver
      case ret of
        Just conflicted -> do
          handleConflict conflictCounter conflicted
          -- TODO: should also learn the PB constraint?
        Nothing -> do
          case pb of
            Nothing -> return Nothing
            Just (lhs,rhs) -> do
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

-- | Cancel exectution of 'solve' or 'solveWith'.
--
-- This can be called from other threads.
cancel :: Solver -> IO ()
cancel solver = writeIORef (svCanceled solver) True

-- | After 'solve' returns True, it returns an satisfying assignment.
getModel :: Solver -> IO Model
getModel solver = do
  m <- readIORef (svModel solver)
  return (fromJust m)

-- | After 'solveWith' returns False, it returns a set of assumptions
-- that leads to contradiction. In particular, if it returns an empty
-- set, the problem is unsatisiable without any assumptions.
getFailedAssumptions :: Solver -> IO [Lit]
getFailedAssumptions solver = readIORef (svFailedAssumptions solver)

-- | __EXPERIMENTAL API__: After 'solveWith' returns True or failed with 'BudgetExceeded' exception,
-- it returns a set of literals that are implied by assumptions.
getAssumptionsImplications :: Solver -> IO [Lit]
getAssumptionsImplications solver = liftM IS.toList $ readIORef (svAssumptionsImplications solver)

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
    modifyIOURef (svNRemovedConstr solver) (+n)
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
  flag <- configEnableForwardSubsumptionRemoval <$> getConfig solver
  if not flag then
    return False
  else do
    withEnablePhaseSaving False $ do
      bracket_
        (pushDecisionLevel solver)
        (backtrackTo solver levelRoot) $ do
          b <- allM (\lit -> assign solver (litNot lit)) lits
          if b then
            liftM isJust (deduce solver)
          else do
            when debugMode $ log solver ("forward subsumption: " ++ show lits)
            return True
  where
    withEnablePhaseSaving flag m =
      bracket
        (getConfig solver)
        (\saved -> modifyConfig solver (\config -> config{ configEnablePhaseSaving = configEnablePhaseSaving saved }))
        (\saved -> setConfig solver saved{ configEnablePhaseSaving = flag } >> m)

removeBackwardSubsumedBy :: Solver -> PBLinAtLeast -> IO ()
removeBackwardSubsumedBy solver pb = do
  flag <- configEnableBackwardSubsumptionRemoval <$> getConfig solver
  when flag $ do
    xs <- backwardSubsumedBy solver pb
    when debugMode $ do
      forM_ (HashSet.toList xs) $ \c -> do
        s <- showConstraintHandler c
        log solver (printf "backward subsumption: %s is subsumed by %s\n" s (show pb))
    removeConstraintHandlers solver xs

backwardSubsumedBy :: Solver -> PBLinAtLeast -> IO (HashSet SomeConstraintHandler)
backwardSubsumedBy solver pb@(lhs,_) = do
  xs <- forM lhs $ \(_,lit) -> do
    Vec.unsafeRead (svLitOccurList solver) (litIndex lit)
  case xs of
    [] -> return HashSet.empty
    s:ss -> do
      let p c = do
            -- Note that @isPBRepresentable c@ is always True here,
            -- because only such constraints are added to occur list.
            -- See 'addToDB'.
            pb2 <- instantiatePBLinAtLeast (getLitFixed solver) =<< toPBLinAtLeast c
            return $ pbLinSubsume pb pb2
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
  modifyIOURef (svNRemovedConstr solver) (+n)
  writeIORef (svConstrDB solver) ys

{--------------------------------------------------------------------
  Parameter settings.
--------------------------------------------------------------------}

{--------------------------------------------------------------------
  Configulation
--------------------------------------------------------------------}

getConfig :: Solver -> IO Config
getConfig solver = readIORef $ svConfig solver

setConfig :: Solver -> Config -> IO ()
setConfig solver conf = do
  orig <- getConfig solver
  writeIORef (svConfig solver) conf
  when (configBranchingStrategy orig /= configBranchingStrategy conf) $ do
    PQ.rebuild (svVarQueue solver)

modifyConfig :: Solver -> (Config -> Config) -> IO ()
modifyConfig solver f = do
  config <- getConfig solver
  setConfig solver $ f config

-- | The default polarity of a variable.
setVarPolarity :: Solver -> Var -> Bool -> IO ()
setVarPolarity solver v val = Vec.unsafeWrite (svVarPolarity solver) (v - 1) val

-- | Set random generator used by the random variable selection
setRandomGen :: Solver -> Rand.GenIO -> IO ()
setRandomGen solver = writeIORef (svRandomGen solver)

-- | Get random generator used by the random variable selection
getRandomGen :: Solver -> IO Rand.GenIO
getRandomGen solver = readIORef (svRandomGen solver)

setConfBudget :: Solver -> Maybe Int -> IO ()
setConfBudget solver (Just b) | b >= 0 = writeIOURef (svConfBudget solver) b
setConfBudget solver _ = writeIOURef (svConfBudget solver) (-1)

{--------------------------------------------------------------------
  API for implementation of @solve@
--------------------------------------------------------------------}

pickBranchLit :: Solver -> IO Lit
pickBranchLit !solver = do
  gen <- readIORef (svRandomGen solver)
  let vqueue = svVarQueue solver
  !randfreq <- configRandomFreq <$> getConfig solver
  !size <- PQ.queueSize vqueue
  -- System.Random.random produces [0,1), but System.Random.MWC.uniform produces (0,1]
  !r <- liftM (1 -) $ Rand.uniform gen
  var <-
    if (r < randfreq && size >= 2) then do
      a <- PQ.getHeapArray vqueue
      i <- Rand.uniformR (0, size-1) gen
      var <- readArray a i
      val <- varValue solver var
      if val == lUndef then do
        modifyIOURef (svNRandomDecision solver) (1+)
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
    -- TODO: random polarity
    p <- Vec.unsafeRead (svVarPolarity solver) (var2 - 1)
    return $! literal var2 p

decide :: Solver -> Lit -> IO ()
decide solver !lit = do
  modifyIOURef (svNDecision solver) (+1)
  pushDecisionLevel solver
  when debugMode $ do
    val <- litValue solver lit
    when (val /= lUndef) $ error "decide: should not happen"
  assign solver lit
  return ()

deduce :: Solver -> IO (Maybe SomeConstraintHandler)
deduce solver = liftM (either Just (const Nothing)) $ runExceptT $ do
  let loop = do
        deduceB solver
        deduceT solver
        empty <- liftIO $ bcpIsEmpty solver
        unless empty $ loop
  loop

deduceB :: Solver -> ExceptT SomeConstraintHandler IO ()
deduceB solver = loop
  where
    loop :: ExceptT SomeConstraintHandler IO ()
    loop = do
      r <- liftIO $ bcpDequeue solver
      case r of
        Nothing -> return ()
        Just lit -> do
          processLit lit
          processVar lit
          loop

    processLit :: Lit -> ExceptT SomeConstraintHandler IO ()
    processLit !lit = ExceptT $ liftM (maybe (Right ()) Left) $ do
      let falsifiedLit = litNot lit
          a = svLitWatches solver
          idx = litIndex falsifiedLit
      let loop2 [] = return Nothing
          loop2 (w:ws) = do
            ok <- propagate solver w falsifiedLit
            if ok then
              loop2 ws
            else do
              Vec.unsafeModify a idx (++ws)
              return (Just w)
      ws <- Vec.unsafeRead a idx
      Vec.unsafeWrite a idx []
      loop2 ws

    processVar :: Lit -> ExceptT SomeConstraintHandler IO ()
    processVar !lit = ExceptT $ liftM (maybe (Right ()) Left) $ do
      let falsifiedLit = litNot lit
          idx = litVar lit - 1
      let loop2 [] = return Nothing
          loop2 (w:ws) = do
            ok <- propagate solver w falsifiedLit
            if ok
              then loop2 ws
              else do
                Vec.unsafeModify (svVarWatches solver) idx (++ws)
                return (Just w)
      ws <- Vec.unsafeRead (svVarWatches solver) idx
      Vec.unsafeWrite (svVarWatches solver) idx []
      loop2 ws

analyzeConflict :: ConstraintHandler c => Solver -> c -> IO (Clause, Level)
analyzeConflict solver constr = do
  config <- getConfig solver
  let isHybrid = configLearningStrategy config == LearningHybrid

  d <- getDecisionLevel solver
  (out :: Vec.UVec Lit) <- Vec.new
  Vec.push out 0 -- (leave room for the asserting literal)
  (pathC :: IOURef Int) <- newIOURef 0

  pbConstrRef <- newIORef undefined

  let f lits = do
        forM_ lits $ \lit -> do
          let !v = litVar lit
          lv <- litLevel solver lit
          b <- Vec.unsafeRead (svSeen solver) (v - 1)
          when (not b && lv > levelRoot) $ do
            varBumpActivity solver v
            varIncrementParticipated solver v
            if lv >= d then do
              Vec.unsafeWrite (svSeen solver) (v - 1) True
              modifyIOURef pathC (+1)
            else do
              Vec.push out lit

      processLitHybrid pb constr2 lit getLits = do
        pb2 <- do
          let clausePB = do
                lits <- getLits
                return $ clauseToPBLinAtLeast (lit : lits)
          b <- isPBRepresentable constr2
          if not b then do
            clausePB
          else do
            pb2 <- toPBLinAtLeast constr2
            o <- pbOverSAT solver pb2
            if o then do
              clausePB
            else
              return pb2
        let pb3 = cutResolve pb pb2 (litVar lit)
            ls = IS.fromList [l | (_,l) <- fst pb3]
        seq ls $ writeIORef pbConstrRef (ls, pb3)

      popUnseen = do
        l <- peekTrail solver
        let !v = litVar l
        b <- Vec.unsafeRead (svSeen solver) (v - 1)
        if b then do
          return ()
        else do
          when isHybrid $ do
            (ls, pb) <- readIORef pbConstrRef
            when (litNot l `IS.member` ls) $ do
              Just constr2 <- varReason solver v
              processLitHybrid pb constr2 l (reasonOf solver constr2 (Just l))
          popTrail solver
          popUnseen

      loop = do
        popUnseen
        l <- peekTrail solver
        let !v = litVar l
        Vec.unsafeWrite (svSeen solver) (v - 1) False
        modifyIOURef pathC (subtract 1)
        c <- readIOURef pathC
        if c > 0 then do
          Just constr2 <- varReason solver v
          constrBumpActivity solver constr2
          lits <- reasonOf solver constr2 (Just l)
          f lits
          when isHybrid $ do
            (ls, pb) <- readIORef pbConstrRef
            when (litNot l `IS.member` ls) $ do
              processLitHybrid pb constr2 l (return lits)
          popTrail solver
          loop
        else do
          Vec.unsafeWrite out 0 (litNot l)

  constrBumpActivity solver constr
  falsifiedLits <- reasonOf solver constr Nothing
  f falsifiedLits
  when isHybrid $ do
     pb <- do
       b <- isPBRepresentable constr
       if b then
         toPBLinAtLeast constr
       else
         return (clauseToPBLinAtLeast falsifiedLits)
     let ls = IS.fromList [l | (_,l) <- fst pb]
     seq ls $ writeIORef pbConstrRef (ls, pb)
  loop
  lits <- liftM IS.fromList $ Vec.getElems out

  lits2 <- minimizeConflictClause solver lits

  incrementReasoned solver (IS.toList lits2)

  xs <- liftM (sortBy (flip (comparing snd))) $
    forM (IS.toList lits2) $ \l -> do
      lv <- litLevel solver l
      return (l,lv)

  when isHybrid $ do
    (_, pb) <- readIORef pbConstrRef
    case pbToClause pb of
      Just _ -> writeIORef (svPBLearnt solver) Nothing
      Nothing -> writeIORef (svPBLearnt solver) (Just pb)

  let level = case xs of
                [] -> error "analyzeConflict: should not happen"
                [_] -> levelRoot
                _:(_,lv):_ -> lv
  return (map fst xs, level)

-- { p } ∪ { pにfalseを割り当てる原因のassumption }
analyzeFinal :: Solver -> Lit -> IO [Lit]
analyzeFinal solver p = do
  let go :: Int -> VarSet -> [Lit] -> IO [Lit]
      go i seen result
        | i < 0 = return result
        | otherwise = do
            l <- Vec.unsafeRead (svTrail solver) i
            lv <- litLevel solver l
            if lv == levelRoot then
              return result
            else if litVar l `IS.member` seen then do
              r <- varReason solver (litVar l)
              case r of
                Nothing -> do
                  let seen' = IS.delete (litVar l) seen
                  go (i-1) seen' (l : result)
                Just constr  -> do
                  c <- reasonOf solver constr (Just l)
                  let seen' = IS.delete (litVar l) seen `IS.union` IS.fromList [litVar l2 | l2 <- c]
                  go (i-1) seen' result
            else
              go (i-1) seen result
  n <- Vec.getSize (svTrail solver)
  go (n-1) (IS.singleton (litVar p)) [p]

pbBacktrackLevel :: Solver -> PBLinAtLeast -> IO Level
pbBacktrackLevel _ ([], rhs) = assert (rhs > 0) $ return levelRoot
pbBacktrackLevel solver (lhs, rhs) = do
  levelToLiterals <- liftM (IM.unionsWith IM.union) $ forM lhs $ \(c,lit) -> do
    val <- litValue solver lit
    if val /= lUndef then do
      level <- litLevel solver lit
      return $ IM.singleton level (IM.singleton lit (c,val))
    else
      return $ IM.singleton maxBound (IM.singleton lit (c,val))

  let replay [] !_ = error "pbBacktrackLevel: should not happen"
      replay ((lv,lv_lits) : lvs) !slack = do
        let slack_lv = slack - sum [c | (_,(c,val)) <- IM.toList lv_lits, val == lFalse]
        if slack_lv < 0 then
          return lv -- CONFLICT
        else if any (\(_, lits2) -> any (\(c,_) -> c > slack_lv) (IM.elems lits2)) lvs then
          return lv -- UNIT
        else
          replay lvs slack_lv

  let initial_slack = sum [c | (c,_) <- lhs] - rhs
  if any (\(c,_) -> c > initial_slack) lhs then
    return 0
  else do
    replay (IM.toList levelToLiterals) initial_slack

minimizeConflictClause :: Solver -> LitSet -> IO LitSet
minimizeConflictClause solver lits = do
  ccmin <- configCCMin <$> getConfig solver
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

incrementReasoned :: Solver -> Clause -> IO ()
incrementReasoned solver ls = do
  let f reasonSided l = do
        m <- varReason solver (litVar l)
        case m of
          Nothing -> return reasonSided
          Just constr -> do
            v <- litValue solver l
            unless (v == lFalse) undefined
            xs <- constrReasonOf solver constr (Just (litNot l))
            return $ reasonSided `IS.union` IS.fromList (map litVar xs)
  reasonSided <- foldM f IS.empty ls
  mapM_ (varIncrementReasoned solver) (IS.toList reasonSided)

peekTrail :: Solver -> IO Lit
peekTrail solver = do
  n <- Vec.getSize (svTrail solver)
  Vec.unsafeRead (svTrail solver) (n-1)

popTrail :: Solver -> IO Lit
popTrail solver = do
  l <- Vec.unsafePop (svTrail solver)
  unassign solver (litVar l)
  return l

getDecisionLevel ::Solver -> IO Int
getDecisionLevel solver = Vec.getSize (svTrailLimit solver)

pushDecisionLevel :: Solver -> IO ()
pushDecisionLevel solver = do
  Vec.push (svTrailLimit solver) =<< Vec.getSize (svTrail solver)
  mt <- getTheory solver
  case mt of
    Nothing -> return ()
    Just t -> thPushBacktrackPoint t

popDecisionLevel :: Solver -> IO ()
popDecisionLevel solver = do
  n <- Vec.unsafePop (svTrailLimit solver)
  let loop = do
        m <- Vec.getSize (svTrail solver)
        when (m > n) $ do
          popTrail solver
          loop
  loop
  mt <- getTheory solver
  case mt of
    Nothing -> return ()
    Just t -> thPopBacktrackPoint t

-- | Revert to the state at given level
-- (keeping all assignment at @level@ but not beyond).
backtrackTo :: Solver -> Int -> IO ()
backtrackTo solver level = do
  when debugMode $ log solver $ printf "backtrackTo: %d" level
  loop
  bcpClear solver
  mt <- getTheory solver
  case mt of
    Nothing -> return ()
    Just _ -> do
      n <- Vec.getSize (svTrail solver)
      writeIOURef (svTheoryChecked solver) n
  where
    loop :: IO ()
    loop = do
      lv <- getDecisionLevel solver
      when (lv > level) $ do
        popDecisionLevel solver
        loop

constructModel :: Solver -> IO ()
constructModel solver = do
  n <- getNVars solver
  (marr::IOUArray Var Bool) <- newArray_ (1,n)
  forLoop 1 (<=n) (+1) $ \v -> do
    val <- varValue solver v
    writeArray marr v (fromJust (unliftBool val))
  m <- unsafeFreeze marr
  writeIORef (svModel solver) (Just m)

saveAssumptionsImplications :: Solver -> IO ()
saveAssumptionsImplications solver = do
  n <- Vec.getSize (svAssumptions solver)
  lv <- getDecisionLevel solver

  lim_beg <-
    if lv == 0 then
      return 0
    else
      Vec.read (svTrailLimit solver) 0
  lim_end <-
    if lv > n then
       Vec.read (svTrailLimit solver) n
    else
       Vec.getSize (svTrail solver)

  let ref = svAssumptionsImplications solver
  forM_ [lim_beg .. lim_end-1] $ \i -> do
    lit <- Vec.read (svTrail solver) i
    modifyIORef' ref (IS.insert lit)
  forM_ [0..n-1] $ \i -> do
    lit <- Vec.read (svAssumptions solver) i
    modifyIORef' ref (IS.delete lit)

constrDecayActivity :: Solver -> IO ()
constrDecayActivity solver = do
  d <- configConstrDecay <$> getConfig solver
  modifyIOURef (svConstrInc solver) (d*)

constrBumpActivity :: ConstraintHandler a => Solver -> a -> IO ()
constrBumpActivity solver this = do
  aval <- constrReadActivity this
  when (aval >= 0) $ do -- learnt clause
    inc <- readIOURef (svConstrInc solver)
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
  modifyIOURef (svConstrInc solver) (* 1e-20)

resetStat :: Solver -> IO ()
resetStat solver = do
  writeIOURef (svNDecision solver) 0
  writeIOURef (svNRandomDecision solver) 0
  writeIOURef (svNConflict solver) 0
  writeIOURef (svNRestart solver) 0
  writeIOURef (svNLearntGC solver) 0

printStatHeader :: Solver -> IO ()
printStatHeader solver = do
  log solver $ "============================[ Search Statistics ]============================"
  log solver $ " Time | Restart | Decision | Conflict |      LEARNT     | Fixed    | Removed "
  log solver $ "      |         |          |          |    Limit     GC | Var      | Constra "
  log solver $ "============================================================================="

printStat :: Solver -> Bool -> IO ()
printStat solver force = do
  nowWC <- getTime Monotonic
  b <- if force
       then return True
       else do
         lastWC <- readIORef (svLastStatWC solver)
         return $ sec (nowWC `diffTimeSpec` lastWC) > 1
  when b $ do
    startWC   <- readIORef (svStartWC solver)
    let tm = showTimeDiff $ nowWC `diffTimeSpec` startWC
    restart   <- readIOURef (svNRestart solver)
    dec       <- readIOURef (svNDecision solver)
    conflict  <- readIOURef (svNConflict solver)
    learntLim <- readIORef (svLearntLim solver)
    learntGC  <- readIOURef (svNLearntGC solver)
    fixed     <- getNFixed solver
    removed   <- readIOURef (svNRemovedConstr solver)
    log solver $ printf "%s | %7d | %8d | %8d | %8d %6d | %8d | %8d"
      tm restart dec conflict learntLim learntGC fixed removed
    writeIORef (svLastStatWC solver) nowWC

showTimeDiff :: TimeSpec -> String
showTimeDiff t
  | si <  100  = printf "%4.1fs" (fromRational s :: Double)
  | si <= 9999 = printf "%4ds" si
  | mi <  100  = printf "%4.1fm" (fromRational m :: Double)
  | mi <= 9999 = printf "%4dm" mi
  | hi <  100  = printf "%4.1fs" (fromRational h :: Double)
  | otherwise  = printf "%4dh" hi
  where
    s :: Rational
    s = fromIntegral (toNanoSecs t) / 10^(9::Int)

    si :: Integer
    si = fromIntegral (sec t)

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

  showConstraintHandler :: a -> IO String

  constrAttach :: Solver -> SomeConstraintHandler -> a -> IO Bool

  constrDetach :: Solver -> SomeConstraintHandler -> a -> IO ()

  constrIsLocked :: Solver -> SomeConstraintHandler -> a -> IO Bool

  -- | invoked with the watched literal when the literal is falsified.
  -- 'watch' で 'toConstraint' を呼び出して heap allocation が発生するのを
  -- 避けるために、元の 'SomeConstraintHandler' も渡しておく。
  constrPropagate :: Solver -> SomeConstraintHandler -> a -> Lit -> IO Bool

  -- | deduce a clause C∨l from the constraint and return C.
  -- C and l should be false and true respectively under the current
  -- assignment.
  constrReasonOf :: Solver -> a -> Maybe Lit -> IO Clause

  constrOnUnassigned :: Solver -> SomeConstraintHandler -> a -> Lit -> IO ()

  isPBRepresentable :: a -> IO Bool
  toPBLinAtLeast :: a -> IO PBLinAtLeast

  isSatisfied :: Solver -> a -> IO Bool

  constrIsProtected :: Solver -> a -> IO Bool
  constrIsProtected _ _ = return False

  constrWeight :: Solver -> a -> IO Double
  constrWeight _ _ = return 1.0

  constrReadActivity :: a -> IO Double

  constrWriteActivity :: a -> Double -> IO ()

attach :: Solver -> SomeConstraintHandler -> IO Bool
attach solver c = constrAttach solver c c

detach :: Solver -> SomeConstraintHandler -> IO ()
detach solver c = do
  constrDetach solver c c
  b <- isPBRepresentable c
  when b $ do
    (lhs,_) <- toPBLinAtLeast c
    forM_ lhs $ \(_,lit) -> do
      Vec.unsafeModify (svLitOccurList solver) (litIndex lit) (HashSet.delete c)

-- | invoked with the watched literal when the literal is falsified.
propagate :: Solver -> SomeConstraintHandler -> Lit -> IO Bool
propagate solver c l = constrPropagate solver c c l

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
          str <- showConstraintHandler c
          error (printf "reasonOf: value of literal %d should be True but %s (constrReasonOf %s %s)" lit (show val) str (show x))
  cl <- constrReasonOf solver c x
  when debugMode $ do
    forM_ cl $ \lit -> do
      val <- litValue solver lit
      unless (lFalse == val) $ do
        str <- showConstraintHandler c
        error (printf "reasonOf: value of literal %d should be False but %s (constrReasonOf %s %s)" lit (show val) str (show x))
  return cl

isLocked :: Solver -> SomeConstraintHandler -> IO Bool
isLocked solver c = constrIsLocked solver c c

data SomeConstraintHandler
  = CHClause !ClauseHandler
  | CHAtLeast !AtLeastHandler
  | CHPBCounter !PBHandlerCounter
  | CHPBPueblo !PBHandlerPueblo
  | CHXORClause !XORClauseHandler
  | CHTheory !TheoryHandler
  deriving Eq

instance Hashable SomeConstraintHandler where
  hashWithSalt s (CHClause c)    = s `hashWithSalt` (0::Int) `hashWithSalt` c
  hashWithSalt s (CHAtLeast c)   = s `hashWithSalt` (1::Int) `hashWithSalt` c
  hashWithSalt s (CHPBCounter c) = s `hashWithSalt` (2::Int) `hashWithSalt` c
  hashWithSalt s (CHPBPueblo c)  = s `hashWithSalt` (3::Int) `hashWithSalt` c
  hashWithSalt s (CHXORClause c) = s `hashWithSalt` (4::Int) `hashWithSalt` c
  hashWithSalt s (CHTheory c)    = s `hashWithSalt` (5::Int) `hashWithSalt` c

instance ConstraintHandler SomeConstraintHandler where
  toConstraintHandler = id

  showConstraintHandler (CHClause c)    = showConstraintHandler c
  showConstraintHandler (CHAtLeast c)   = showConstraintHandler c
  showConstraintHandler (CHPBCounter c) = showConstraintHandler c
  showConstraintHandler (CHPBPueblo c)  = showConstraintHandler c
  showConstraintHandler (CHXORClause c) = showConstraintHandler c
  showConstraintHandler (CHTheory c)    = showConstraintHandler c

  constrAttach solver this (CHClause c)    = constrAttach solver this c
  constrAttach solver this (CHAtLeast c)   = constrAttach solver this c
  constrAttach solver this (CHPBCounter c) = constrAttach solver this c
  constrAttach solver this (CHPBPueblo c)  = constrAttach solver this c
  constrAttach solver this (CHXORClause c) = constrAttach solver this c
  constrAttach solver this (CHTheory c)    = constrAttach solver this c

  constrDetach solver this (CHClause c)    = constrDetach solver this c
  constrDetach solver this (CHAtLeast c)   = constrDetach solver this c
  constrDetach solver this (CHPBCounter c) = constrDetach solver this c
  constrDetach solver this (CHPBPueblo c)  = constrDetach solver this c
  constrDetach solver this (CHXORClause c) = constrDetach solver this c
  constrDetach solver this (CHTheory c)    = constrDetach solver this c

  constrIsLocked solver this (CHClause c)    = constrIsLocked solver this c
  constrIsLocked solver this (CHAtLeast c)   = constrIsLocked solver this c
  constrIsLocked solver this (CHPBCounter c) = constrIsLocked solver this c
  constrIsLocked solver this (CHPBPueblo c)  = constrIsLocked solver this c
  constrIsLocked solver this (CHXORClause c) = constrIsLocked solver this c
  constrIsLocked solver this (CHTheory c)    = constrIsLocked solver this c

  constrPropagate solver this (CHClause c)  lit   = constrPropagate solver this c lit
  constrPropagate solver this (CHAtLeast c) lit   = constrPropagate solver this c lit
  constrPropagate solver this (CHPBCounter c) lit = constrPropagate solver this c lit
  constrPropagate solver this (CHPBPueblo c) lit  = constrPropagate solver this c lit
  constrPropagate solver this (CHXORClause c) lit = constrPropagate solver this c lit
  constrPropagate solver this (CHTheory c) lit    = constrPropagate solver this c lit

  constrReasonOf solver (CHClause c)  l   = constrReasonOf solver c l
  constrReasonOf solver (CHAtLeast c) l   = constrReasonOf solver c l
  constrReasonOf solver (CHPBCounter c) l = constrReasonOf solver c l
  constrReasonOf solver (CHPBPueblo c) l  = constrReasonOf solver c l
  constrReasonOf solver (CHXORClause c) l = constrReasonOf solver c l
  constrReasonOf solver (CHTheory c) l    = constrReasonOf solver c l

  constrOnUnassigned solver this (CHClause c)  l   = constrOnUnassigned solver this c l
  constrOnUnassigned solver this (CHAtLeast c) l   = constrOnUnassigned solver this c l
  constrOnUnassigned solver this (CHPBCounter c) l = constrOnUnassigned solver this c l
  constrOnUnassigned solver this (CHPBPueblo c) l  = constrOnUnassigned solver this c l
  constrOnUnassigned solver this (CHXORClause c) l = constrOnUnassigned solver this c l
  constrOnUnassigned solver this (CHTheory c) l    = constrOnUnassigned solver this c l

  isPBRepresentable (CHClause c)    = isPBRepresentable c
  isPBRepresentable (CHAtLeast c)   = isPBRepresentable c
  isPBRepresentable (CHPBCounter c) = isPBRepresentable c
  isPBRepresentable (CHPBPueblo c)  = isPBRepresentable c
  isPBRepresentable (CHXORClause c) = isPBRepresentable c
  isPBRepresentable (CHTheory c)    = isPBRepresentable c

  toPBLinAtLeast (CHClause c)    = toPBLinAtLeast c
  toPBLinAtLeast (CHAtLeast c)   = toPBLinAtLeast c
  toPBLinAtLeast (CHPBCounter c) = toPBLinAtLeast c
  toPBLinAtLeast (CHPBPueblo c)  = toPBLinAtLeast c
  toPBLinAtLeast (CHXORClause c) = toPBLinAtLeast c
  toPBLinAtLeast (CHTheory c)    = toPBLinAtLeast c

  isSatisfied solver (CHClause c)    = isSatisfied solver c
  isSatisfied solver (CHAtLeast c)   = isSatisfied solver c
  isSatisfied solver (CHPBCounter c) = isSatisfied solver c
  isSatisfied solver (CHPBPueblo c)  = isSatisfied solver c
  isSatisfied solver (CHXORClause c) = isSatisfied solver c
  isSatisfied solver (CHTheory c)    = isSatisfied solver c

  constrIsProtected solver (CHClause c)    = constrIsProtected solver c
  constrIsProtected solver (CHAtLeast c)   = constrIsProtected solver c
  constrIsProtected solver (CHPBCounter c) = constrIsProtected solver c
  constrIsProtected solver (CHPBPueblo c)  = constrIsProtected solver c
  constrIsProtected solver (CHXORClause c) = constrIsProtected solver c
  constrIsProtected solver (CHTheory c)    = constrIsProtected solver c

  constrReadActivity (CHClause c)    = constrReadActivity c
  constrReadActivity (CHAtLeast c)   = constrReadActivity c
  constrReadActivity (CHPBCounter c) = constrReadActivity c
  constrReadActivity (CHPBPueblo c)  = constrReadActivity c
  constrReadActivity (CHXORClause c) = constrReadActivity c
  constrReadActivity (CHTheory c)    = constrReadActivity c

  constrWriteActivity (CHClause c)    aval = constrWriteActivity c aval
  constrWriteActivity (CHAtLeast c)   aval = constrWriteActivity c aval
  constrWriteActivity (CHPBCounter c) aval = constrWriteActivity c aval
  constrWriteActivity (CHPBPueblo c)  aval = constrWriteActivity c aval
  constrWriteActivity (CHXORClause c) aval = constrWriteActivity c aval
  constrWriteActivity (CHTheory c)    aval = constrWriteActivity c aval

isReasonOf :: Solver -> SomeConstraintHandler -> Lit -> IO Bool
isReasonOf solver c lit = do
  val <- litValue solver lit
  if val == lUndef then
    return False
  else do
    m <- varReason solver (litVar lit)
    case m of
      Nothing -> return False
      Just c2  -> return $! c == c2

-- To avoid heap-allocation Maybe value, it returns -1 when not found.
findForWatch :: Solver -> LitArray -> Int -> Int -> IO Int
#ifndef __GLASGOW_HASKELL__
findForWatch solver a beg end = go beg end
  where
    go :: Int -> Int -> IO Int
    go i end | i > end = return (-1)
    go i end = do
      val <- litValue s =<< readLitArray a i
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
    go# i end' w | isTrue# (i ># end') = (# w, -1# #)
    go# i end' w =
      case unIO (litValue solver =<< readLitArray a (I# i)) w of
        (# w2, val #) ->
          if val /= lFalse
            then (# w2, i #)
            else go# (i +# 1#) end' w2

    unIO (IO f) = f
#endif

-- To avoid heap-allocating Maybe value, it returns -1 when not found.
findForWatch2 :: Solver -> LitArray -> Int -> Int -> IO Int
#ifndef __GLASGOW_HASKELL__
findForWatch2 solver a beg end = go beg end
  where
    go :: Int -> Int -> IO Int
    go i end | i > end = return (-1)
    go i end = do
      val <- litValue s =<< readLitArray a i
      if val == lUndef
        then return i
        else go (i+1) end
#else
{- We performed worker-wrapper transfomation manually, since the worker
   generated by GHC has type
   "Int# -> Int# -> State# RealWorld -> (# State# RealWorld, Int #)",
   not "Int# -> Int# -> State# RealWorld -> (# State# RealWorld, Int# #)".
   We want latter one to avoid heap-allocating Int value. -}
findForWatch2 solver a (I# beg) (I# end) = IO $ \w ->
  case go# beg end w of
    (# w2, ret #) -> (# w2, I# ret #)
  where
    go# :: Int# -> Int# -> State# RealWorld -> (# State# RealWorld, Int# #)
    go# i end w | isTrue# (i ># end) = (# w, -1# #)
    go# i end w =
      case unIO (litValue solver =<< readLitArray a (I# i)) w of
        (# w2, val #) ->
          if val == lUndef
            then (# w2, i #)
            else go# (i +# 1#) end w2

    unIO (IO f) = f
#endif

{--------------------------------------------------------------------
  Clause
--------------------------------------------------------------------}

data ClauseHandler
  = ClauseHandler
  { claLits :: !LitArray
  , claActivity :: !(IORef Double)
  , claHash :: !Int
  }

claGetSize :: ClauseHandler -> IO Int
claGetSize cla = getLitArraySize (claLits cla)

instance Eq ClauseHandler where
  (==) = (==) `on` claLits

instance Hashable ClauseHandler where
  hash = claHash
  hashWithSalt = defaultHashWithSalt

newClauseHandler :: Clause -> Bool -> IO ClauseHandler
newClauseHandler ls learnt = do
  a <- newLitArray ls
  act <- newIORef $! (if learnt then 0 else -1)
  return (ClauseHandler a act (hash ls))

instance ConstraintHandler ClauseHandler where
  toConstraintHandler = CHClause

  showConstraintHandler this = do
    lits <- getLits (claLits this)
    return (show lits)

  constrAttach solver this this2 = do
    -- BCP Queue should be empty at this point.
    -- If not, duplicated propagation happens.
    bcpCheckEmpty solver

    size <- claGetSize this2
    if size == 0 then do
      markBad solver
      return False
    else if size == 1 then do
      lit0 <- readLitArray (claLits this2) 0
      assignBy solver lit0 this
    else do
      ref <- newIORef 1
      let f i = do
            lit_i <- readLitArray (claLits this2) i
            val_i <- litValue solver lit_i
            if val_i /= lFalse then
              return True
            else do
              j <- readIORef ref
              k <- findForWatch solver (claLits this2) j (size - 1)
              case k of
                -1 -> do
                  return False
                _ -> do
                  lit_k <- readLitArray (claLits this2) k
                  writeLitArray (claLits this2) i lit_k
                  writeLitArray (claLits this2) k lit_i
                  writeIORef ref $! (k+1)
                  return True

      b <- f 0
      if b then do
        lit0 <- readLitArray (claLits this2) 0
        watchLit solver lit0 this
        b2 <- f 1
        if b2 then do
          lit1 <- readLitArray (claLits this2) 1
          watchLit solver lit1 this
          return True
        else do -- UNIT
          -- We need to watch the most recently falsified literal
          (i,_) <- liftM (maximumBy (comparing snd)) $ forM [1..size-1] $ \l -> do
            lit <- readLitArray (claLits this2) l
            lv <- litLevel solver lit
            return (l,lv)
          lit1 <- readLitArray (claLits this2) 1
          liti <- readLitArray (claLits this2) i
          writeLitArray (claLits this2) 1 liti
          writeLitArray (claLits this2) i lit1
          watchLit solver liti this
          assignBy solver lit0 this -- should always succeed
      else do -- CONFLICT
        ls <- liftM (map fst . sortBy (flip (comparing snd))) $ forM [0..size-1] $ \l -> do
          lit <- readLitArray (claLits this2) l
          lv <- litLevel solver lit
          return (l,lv)
        forM_ (zip [0..] ls) $ \(i,lit) -> do
          writeLitArray (claLits this2) i lit
        lit0 <- readLitArray (claLits this2) 0
        lit1 <- readLitArray (claLits this2) 1
        watchLit solver lit0 this
        watchLit solver lit1 this
        return False

  constrDetach solver this this2 = do
    size <- claGetSize this2
    when (size >= 2) $ do
      lit0 <- readLitArray (claLits this2) 0
      lit1 <- readLitArray (claLits this2) 1
      unwatchLit solver lit0 this
      unwatchLit solver lit1 this

  constrIsLocked solver this this2 = do
    size <- claGetSize this2
    if size < 2 then
      return False
    else do
      lit <- readLitArray (claLits this2) 0
      isReasonOf solver this lit

  constrPropagate !solver this this2 !falsifiedLit = do
    preprocess

    !lit0 <- readLitArray a 0
    !val0 <- litValue solver lit0
    if val0 == lTrue then do
      watchLit solver falsifiedLit this
      return True
    else do
      size <- claGetSize this2
      i <- findForWatch solver a 2 (size - 1)
      case i of
        -1 -> do
          when debugMode $ logIO solver $ do
             str <- showConstraintHandler this
             return $ printf "constrPropagate: %s is unit" str
          watchLit solver falsifiedLit this
          assignBy solver lit0 this
        _  -> do
          !lit1 <- readLitArray a 1
          !liti <- readLitArray a i
          writeLitArray a 1 liti
          writeLitArray a i lit1
          watchLit solver liti this
          return True

    where
      a = claLits this2

      preprocess :: IO ()
      preprocess = do
        !l0 <- readLitArray a 0
        !l1 <- readLitArray a 1
        assert (l0==falsifiedLit || l1==falsifiedLit) $ return ()
        when (l0==falsifiedLit) $ do
          writeLitArray a 0 l1
          writeLitArray a 1 l0

  constrReasonOf _ this l = do
    lits <- getLits (claLits this)
    case l of
      Nothing -> return lits
      Just lit -> do
        assert (lit == head lits) $ return ()
        return $ tail lits

  constrOnUnassigned _solver _this _this2 _lit = return ()

  isPBRepresentable _ = return True

  toPBLinAtLeast this = do
    lits <- getLits (claLits this)
    return ([(1,l) | l <- lits], 1)

  isSatisfied solver this = do
    n <- getLitArraySize (claLits this)
    liftM isLeft $ runExceptT $ forLoop 0 (<n) (+1) $ \i -> do
      v <- lift $ litValue solver =<< readLitArray (claLits this) i
      when (v == lTrue) $ throwE ()

  constrIsProtected _ this = do
    size <- claGetSize this
    return $! size <= 2

  constrReadActivity this = readIORef (claActivity this)

  constrWriteActivity this aval = writeIORef (claActivity this) $! aval

basicAttachClauseHandler :: Solver -> ClauseHandler -> IO Bool
basicAttachClauseHandler solver this = do
  let constr = toConstraintHandler this
  lits <- getLits (claLits this)
  case lits of
    [] -> do
      markBad solver
      return False
    [l1] -> do
      assignBy solver l1 constr
    l1:l2:_ -> do
      watchLit solver l1 constr
      watchLit solver l2 constr
      return True

{--------------------------------------------------------------------
  Cardinality Constraint
--------------------------------------------------------------------}

data AtLeastHandler
  = AtLeastHandler
  { atLeastLits :: !LitArray
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
  a <- newLitArray ls
  act <- newIORef $! (if learnt then 0 else -1)
  return (AtLeastHandler a n act (hash (ls,n)))

instance ConstraintHandler AtLeastHandler where
  toConstraintHandler = CHAtLeast

  showConstraintHandler this = do
    lits <- getLits (atLeastLits this)
    return $ show lits ++ " >= " ++ show (atLeastNum this)

  -- FIXME: simplify implementation
  constrAttach solver this this2 = do
    -- BCP Queue should be empty at this point.
    -- If not, duplicated propagation happens.
    bcpCheckEmpty solver

    let a = atLeastLits this2
    m <- getLitArraySize a
    let n = atLeastNum this2

    if m < n then do
      markBad solver
      return False
    else if m == n then do
      let f i = do
            lit <- readLitArray a i
            assignBy solver lit this
      allM f [0..n-1]
    else do -- m > n
      let f !i !j
            | i == n = do
                -- NOT VIOLATED: n literals (0 .. n-1) are watched
                k <- findForWatch solver a j (m - 1)
                if k /= -1 then do
                  -- NOT UNIT
                  lit_n <- readLitArray a n
                  lit_k <- readLitArray a k
                  writeLitArray a n lit_k
                  writeLitArray a k lit_n
                  watchLit solver lit_k this
                  -- n+1 literals (0 .. n) are watched.
                else do
                  -- UNIT
                  forLoop 0 (<n) (+1) $ \l -> do
                    lit <- readLitArray a l
                    _ <- assignBy solver lit this -- should always succeed
                    return ()
                  -- We need to watch the most recently falsified literal
                  (l,_) <- liftM (maximumBy (comparing snd)) $ forM [n..m-1] $ \l -> do
                    lit <- readLitArray a l
                    lv <- litLevel solver lit
                    when debugMode $ do
                      val <- litValue solver lit
                      unless (val == lFalse) $ error "AtLeastHandler.attach: should not happen"
                    return (l,lv)
                  lit_n <- readLitArray a n
                  lit_l <- readLitArray a l
                  writeLitArray a n lit_l
                  writeLitArray a l lit_n
                  watchLit solver lit_l this
                  -- n+1 literals (0 .. n) are watched.
                return True
            | otherwise = do
                assert (i < n && n <= j) $ return ()
                lit_i <- readLitArray a i
                val_i <- litValue solver lit_i
                if val_i /= lFalse then do
                  watchLit solver lit_i this
                  f (i+1) j
                else do
                  k <- findForWatch solver a j (m - 1)
                  if k /= -1 then do
                    lit_k <- readLitArray a k
                    writeLitArray a i lit_k
                    writeLitArray a k lit_i
                    watchLit solver lit_k this
                    f (i+1) (k+1)
                  else do
                    -- CONFLICT
                    -- We need to watch unassigned literals or most recently falsified literals.
                    do xs <- liftM (sortBy (flip (comparing snd))) $ forM [i..m-1] $ \l -> do
                         lit <- readLitArray a l
                         val <- litValue solver lit
                         if val == lFalse then do
                           lv <- litLevel solver lit
                           return (lit, lv)
                         else do
                           return (lit, maxBound)
                       forM_ (zip [i..m-1] xs) $ \(l,(lit,_lv)) -> do
                         writeLitArray a l lit
                    forLoop i (<=n) (+1) $ \l -> do
                      lit_l <- readLitArray a l
                      watchLit solver lit_l this
                    -- n+1 literals (0 .. n) are watched.
                    return False
      f 0 n

  constrDetach solver this this2 = do
    lits <- getLits (atLeastLits this2)
    let n = atLeastNum this2
    when (length lits > n) $ do
      forLoop 0 (<=n) (+1) $ \i -> do
        lit <- readLitArray (atLeastLits this2) i
        unwatchLit solver lit this

  constrIsLocked solver this this2 = do
    size <- getLitArraySize (atLeastLits this2)
    let n = atLeastNum this2
        loop i
          | i > n = return False
          | otherwise = do
              l <- readLitArray (atLeastLits this2) i
              b <- isReasonOf solver this l
              if b then return True else loop (i+1)
    if size >= n+1 then
      loop 0
    else
      return False

  constrPropagate solver this this2 falsifiedLit = do
    preprocess

    when debugMode $ do
      litn <- readLitArray a n
      unless (litn == falsifiedLit) $ error "AtLeastHandler.constrPropagate: should not happen"

    m <- getLitArraySize a
    i <- findForWatch solver a (n+1) (m-1)
    case i of
      -1 -> do
        when debugMode $ logIO solver $ do
          str <- showConstraintHandler this
          return $ printf "constrPropagate: %s is unit" str
        watchLit solver falsifiedLit this
        let loop :: Int -> IO Bool
            loop j
              | j >= n = return True
              | otherwise = do
                  litj <- readLitArray a j
                  ret2 <- assignBy solver litj this
                  if ret2
                    then loop (j+1)
                    else return False
        loop 0
      _ -> do
        liti <- readLitArray a i
        litn <- readLitArray a n
        writeLitArray a i litn
        writeLitArray a n liti
        watchLit solver liti this
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
              li <- readLitArray a i
              if (li /= falsifiedLit) then
                loop (i+1)
              else do
                ln <- readLitArray a n
                writeLitArray a n li
                writeLitArray a i ln

  constrReasonOf solver this concl = do
    m <- getLitArraySize (atLeastLits this)
    let n = atLeastNum this
    falsifiedLits <- mapM (readLitArray (atLeastLits this)) [n..m-1] -- drop first n elements
    when debugMode $ do
      forM_ falsifiedLits $ \lit -> do
        val <- litValue solver lit
        unless (val == lFalse) $ do
          error $ printf "AtLeastHandler.constrReasonOf: %d is %s (lFalse expected)" lit (show val)
    case concl of
      Nothing -> do
        let go :: Int -> IO Lit
            go i
              | i >= n = error $ printf "AtLeastHandler.constrReasonOf: cannot find falsified literal in first %d elements" n
              | otherwise = do
                  lit <- readLitArray (atLeastLits this) i
                  val <- litValue solver lit
                  if val == lFalse
                  then return lit
                  else go (i+1)
        lit <- go 0
        return $ lit : falsifiedLits
      Just lit -> do
        when debugMode $ do
          es <- getLits (atLeastLits this)
          unless (lit `elem` take n es) $
            error $ printf "AtLeastHandler.constrReasonOf: cannot find %d in first %d elements" n
        return falsifiedLits

  constrOnUnassigned _solver _this _this2 _lit = return ()

  isPBRepresentable _ = return True

  toPBLinAtLeast this = do
    lits <- getLits (atLeastLits this)
    return ([(1,l) | l <- lits], fromIntegral (atLeastNum this))

  isSatisfied solver this = do
    m <- getLitArraySize (atLeastLits this)
    liftM isLeft $ runExceptT $ numLoopState 0 (m-1) 0 $ \(!n) i -> do
      v <- lift $ litValue solver =<< readLitArray (atLeastLits this) i
      if v /= lTrue then do
        return n
      else do
        let n' = n + 1
        when (n' >= atLeastNum this) $ throwE ()
        return n'

  constrReadActivity this = readIORef (atLeastActivity this)

  constrWriteActivity this aval = writeIORef (atLeastActivity this) $! aval

basicAttachAtLeastHandler :: Solver -> AtLeastHandler -> IO Bool
basicAttachAtLeastHandler solver this = do
  lits <- getLits (atLeastLits this)
  let m = length lits
      n = atLeastNum this
      constr = toConstraintHandler this
  if m < n then do
    markBad solver
    return False
  else if m == n then do
    allM (\l -> assignBy solver l constr) lits
  else do -- m > n
    forM_ (take (n+1) lits) $ \l -> watchLit solver l constr
    return True

{--------------------------------------------------------------------
  Pseudo Boolean Constraint
--------------------------------------------------------------------}

newPBHandler :: Solver -> PBLinSum -> Integer -> Bool -> IO SomeConstraintHandler
newPBHandler solver ts degree learnt = do
  config <- configPBHandlerType <$> getConfig solver
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

pbToClause :: PBLinAtLeast -> Maybe Clause
pbToClause pb = do
  (lhs, rhs) <- pbToAtLeast pb
  guard $ rhs == 1
  return lhs

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

  showConstraintHandler this = do
    return $ show (pbTerms this) ++ " >= " ++ show (pbDegree this)

  constrAttach solver this this2 = do
    -- BCP queue should be empty at this point.
    -- It is important for calculating slack.
    bcpCheckEmpty solver
    s <- liftM sum $ forM (pbTerms this2) $ \(c,l) -> do
      watchLit solver l this
      val <- litValue solver l
      if val == lFalse then do
        addOnUnassigned solver this l
        return 0
      else do
        return c
    let slack = s - pbDegree this2
    writeIORef (pbSlack this2) $! slack
    if slack < 0 then
      return False
    else do
      flip allM (pbTerms this2) $ \(c,l) -> do
        val <- litValue solver l
        if c > slack && val == lUndef then do
          assignBy solver l this
        else
          return True

  constrDetach solver this this2 = do
    forM_ (pbTerms this2) $ \(_,l) -> do
      unwatchLit solver l this

  constrIsLocked solver this this2 = do
    anyM (\(_,l) -> isReasonOf solver this l) (pbTerms this2)

  constrPropagate solver this this2 falsifiedLit = do
    watchLit solver falsifiedLit this
    let c = pbCoeffMap this2 IM.! falsifiedLit
    modifyIORef' (pbSlack this2) (subtract c)
    addOnUnassigned solver this falsifiedLit
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

  constrReasonOf solver this l = do
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
          go _ [] _ = error "PBHandlerCounter.constrReasonOf: should not happen"
          go s ((c,lit):xs) ret = do
            val <- litValue solver lit
            if val == lFalse then do
              b <- p lit
              if b
              then go (s - c) xs (lit:ret)
              else go s xs ret
            else do
              go s xs ret

  constrOnUnassigned _solver _this this2 lit = do
    let c = pbCoeffMap this2 IM.! (- lit)
    modifyIORef' (pbSlack this2) (+ c)

  isPBRepresentable _ = return True

  toPBLinAtLeast this = do
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
  watchLit solver lit constr
  modifyIORef' (puebloWatches pb) (IS.insert lit)
  modifyIORef' (puebloWatchSum pb) (+c)

puebloUnwatch :: Solver -> PBHandlerPueblo -> PBLinTerm -> IO ()
puebloUnwatch _solver pb (c, lit) = do
  modifyIORef' (puebloWatches pb) (IS.delete lit)
  modifyIORef' (puebloWatchSum pb) (subtract c)

instance ConstraintHandler PBHandlerPueblo where
  toConstraintHandler = CHPBPueblo

  showConstraintHandler this = do
    return $ show (puebloTerms this) ++ " >= " ++ show (puebloDegree this)

  constrAttach solver this this2 = do
    bcpCheckEmpty solver
    ret <- puebloPropagate solver this this2

    -- register to watch recently falsified literals to recover
    -- "WatchSum >= puebloDegree this + puebloAMax this" when backtrack is performed.
    wsum <- puebloGetWatchSum this2
    unless (wsum >= puebloDegree this2 + puebloAMax this2) $ do
      let f m tm@(_,lit) = do
            val <- litValue solver lit
            if val == lFalse then do
              idx <- varAssignNo solver (litVar lit)
              return (IM.insert idx tm m)
            else
              return m
      xs <- liftM (map snd . IM.toDescList) $ foldM f IM.empty (puebloTerms this2)
      let g !_ [] = return ()
          g !s ((c,l):ts) = do
            addOnUnassigned solver this l
            if s+c >= puebloDegree this2 + puebloAMax this2 then return ()
            else g (s+c) ts
      g wsum xs

    return ret

  constrDetach solver this this2 = do
    ws <- readIORef (puebloWatches this2)
    forM_ (IS.toList ws) $ \l -> do
      unwatchLit solver l this

  constrIsLocked solver this this2 = do
    anyM (\(_,l) -> isReasonOf solver this l) (puebloTerms this2)

  constrPropagate solver this this2 falsifiedLit = do
    let t = fromJust $ find (\(_,l) -> l==falsifiedLit) (puebloTerms this2)
    puebloUnwatch solver this2 t
    ret <- puebloPropagate solver this this2
    wsum <- puebloGetWatchSum this2
    unless (wsum >= puebloDegree this2 + puebloAMax this2) $
      addOnUnassigned solver this falsifiedLit
    return ret

  constrReasonOf solver this l = do
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
          go _ [] _ = error "PBHandlerPueblo.constrReasonOf: should not happen"
          go s ((c,lit):xs) ret = do
            val <- litValue solver lit
            if val == lFalse then do
              b <- p lit
              if b
              then go (s - c) xs (lit:ret)
              else go s xs ret
            else do
              go s xs ret

  constrOnUnassigned solver this this2 lit = do
    let t = fromJust $ find (\(_,l) -> l == - lit) (puebloTerms this2)
    puebloWatch solver this this2 t

  isPBRepresentable _ = return True

  toPBLinAtLeast this = do
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
          watchsum' <- puebloGetWatchSum this
          if watchsum' - c >= puebloDegree this then
            return True
          else do
            val <- litValue solver lit
            when (val == lUndef) $ do
              b <- assignBy solver lit constr
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
  XOR Clause
--------------------------------------------------------------------}

data XORClauseHandler
  = XORClauseHandler
  { xorLits :: !LitArray
  , xorActivity :: !(IORef Double)
  , xorHash :: !Int
  }

instance Eq XORClauseHandler where
  (==) = (==) `on` xorLits

instance Hashable XORClauseHandler where
  hash = xorHash
  hashWithSalt = defaultHashWithSalt

newXORClauseHandler :: [Lit] -> Bool -> IO XORClauseHandler
newXORClauseHandler ls learnt = do
  a <- newLitArray ls
  act <- newIORef $! (if learnt then 0 else -1)
  return (XORClauseHandler a act (hash ls))

instance ConstraintHandler XORClauseHandler where
  toConstraintHandler = CHXORClause

  showConstraintHandler this = do
    lits <- getLits (xorLits this)
    return ("XOR " ++ show lits)

  constrAttach solver this this2 = do
    -- BCP Queue should be empty at this point.
    -- If not, duplicated propagation happens.
    bcpCheckEmpty solver

    let a = xorLits this2
    size <- getLitArraySize a

    if size == 0 then do
      markBad solver
      return False
    else if size == 1 then do
      lit0 <- readLitArray a 0
      assignBy solver lit0 this
    else do
      ref <- newIORef 1
      let f i = do
            lit_i <- readLitArray a i
            val_i <- litValue solver lit_i
            if val_i == lUndef then
              return True
            else do
              j <- readIORef ref
              k <- findForWatch2 solver a j (size - 1)
              case k of
                -1 -> do
                  return False
                _ -> do
                  lit_k <- readLitArray a k
                  writeLitArray a i lit_k
                  writeLitArray a k lit_i
                  writeIORef ref $! (k+1)
                  return True

      b <- f 0
      if b then do
        lit0 <- readLitArray a 0
        watchVar solver (litVar lit0) this
        b2 <- f 1
        if b2 then do
          lit1 <- readLitArray a 1
          watchVar solver (litVar lit1) this
          return True
        else do -- UNIT
          -- We need to watch the most recently falsified literal
          (i,_) <- liftM (maximumBy (comparing snd)) $ forM [1..size-1] $ \l -> do
            lit <- readLitArray a l
            lv <- litLevel solver lit
            return (l,lv)
          lit1 <- readLitArray a 1
          liti <- readLitArray a i
          writeLitArray a 1 liti
          writeLitArray a i lit1
          watchVar solver (litVar liti) this
          -- lit0 ⊕ y
          y <- do
            ref' <- newIORef False
            forLoop 1 (<size) (+1) $ \j -> do
              lit_j <- readLitArray a j
              val_j <- litValue solver lit_j
              modifyIORef' ref' (/= fromJust (unliftBool val_j))
            readIORef ref'
          assignBy solver (if y then litNot lit0 else lit0) this -- should always succeed
      else do
        ls <- liftM (map fst . sortBy (flip (comparing snd))) $ forM [0..size-1] $ \l -> do
          lit <- readLitArray a l
          lv <- litLevel solver lit
          return (l,lv)
        forM_ (zip [0..] ls) $ \(i,lit) -> do
          writeLitArray a i lit
        lit0 <- readLitArray a 0
        lit1 <- readLitArray a 1
        watchVar solver (litVar lit0) this
        watchVar solver (litVar lit1) this
        isSatisfied solver this2

  constrDetach solver this this2 = do
    size <- getLitArraySize (xorLits this2)
    when (size >= 2) $ do
      lit0 <- readLitArray (xorLits this2) 0
      lit1 <- readLitArray (xorLits this2) 1
      unwatchVar solver (litVar lit0) this
      unwatchVar solver (litVar lit1) this

  constrIsLocked solver this this2 = do
    lit0 <- readLitArray (xorLits this2) 0
    lit1 <- readLitArray (xorLits this2) 1
    b0 <- isReasonOf solver this lit0
    b1 <- isReasonOf solver this lit1
    return $ b0 || b1

  constrPropagate !solver this this2 !falsifiedLit = do
    b <- constrIsLocked solver this this2
    if b then
      return True
    else do
      preprocess

      !lit0 <- readLitArray a 0
      !size <- getLitArraySize (xorLits this2)
      i <- findForWatch2 solver a 2 (size - 1)
      case i of
        -1 -> do
          when debugMode $ logIO solver $ do
             str <- showConstraintHandler this
             return $ printf "constrPropagate: %s is unit" str
          watchVar solver v this
          -- lit0 ⊕ y
          y <- do
            ref <- newIORef False
            forLoop 1 (<size) (+1) $ \j -> do
              lit_j <- readLitArray a j
              val_j <- litValue solver lit_j
              modifyIORef' ref (/= fromJust (unliftBool val_j))
            readIORef ref
          assignBy solver (if y then litNot lit0 else lit0) this
        _  -> do
          !lit1 <- readLitArray a 1
          !liti <- readLitArray a i
          writeLitArray a 1 liti
          writeLitArray a i lit1
          watchVar solver (litVar liti) this
          return True

    where
      v = litVar falsifiedLit
      a = xorLits this2

      preprocess :: IO ()
      preprocess = do
        !l0 <- readLitArray a 0
        !l1 <- readLitArray a 1
        assert (litVar l0 == v || litVar l1 == v) $ return ()
        when (litVar l0 == v) $ do
          writeLitArray a 0 l1
          writeLitArray a 1 l0

  constrReasonOf solver this l = do
    lits <- getLits (xorLits this)
    xs <-
      case l of
        Nothing -> mapM f lits
        Just lit -> do
         case lits of
           l1:ls -> do
             assert (litVar lit == litVar l1) $ return ()
             mapM f ls
           _ -> error "XORClauseHandler.constrReasonOf: should not happen"
    return xs
    where
      f :: Lit -> IO Lit
      f lit = do
        let v = litVar lit
        val <- varValue solver v
        return $ literal v (not (fromJust (unliftBool val)))

  constrOnUnassigned _solver _this _this2 _lit = return ()

  isPBRepresentable _ = return False

  toPBLinAtLeast _ = error "XORClauseHandler does not support toPBLinAtLeast"

  isSatisfied solver this = do
    lits <- getLits (xorLits this)
    vals <- mapM (litValue solver) lits
    let f x y
          | x == lUndef || y == lUndef = lUndef
          | otherwise = liftBool (x /= y)
    return $ foldl' f lFalse vals == lTrue

  constrIsProtected _ this = do
    size <- getLitArraySize (xorLits this)
    return $! size <= 2

  constrReadActivity this = readIORef (xorActivity this)

  constrWriteActivity this aval = writeIORef (xorActivity this) $! aval

basicAttachXORClauseHandler :: Solver -> XORClauseHandler -> IO Bool
basicAttachXORClauseHandler solver this = do
  lits <- getLits (xorLits this)
  let constr = toConstraintHandler this
  case lits of
    [] -> do
      markBad solver
      return False
    [l1] -> do
      assignBy solver l1 constr
    l1:l2:_ -> do
      watchVar solver (litVar l1) constr
      watchVar solver (litVar l2) constr
      return True

{--------------------------------------------------------------------
  Arbitrary Boolean Theory
--------------------------------------------------------------------}

setTheory :: Solver -> TheorySolver -> IO ()
setTheory solver tsolver = do
  d <- getDecisionLevel solver
  assert (d == levelRoot) $ return ()

  m <- readIORef (svTheorySolver solver)
  case m of
    Just _ -> do
      error $ "ToySolver.SAT.setTheory: cannot replace TheorySolver"
    Nothing -> do
      writeIORef (svTheorySolver solver) (Just tsolver)
      ret <- deduce solver
      case ret of
        Nothing -> return ()
        Just _ -> markBad solver

getTheory :: Solver -> IO (Maybe TheorySolver)
getTheory solver = readIORef (svTheorySolver solver)

deduceT :: Solver -> ExceptT SomeConstraintHandler IO ()
deduceT solver = do
  mt <- liftIO $ readIORef (svTheorySolver solver)
  case mt of
    Nothing -> return ()
    Just t -> do
      n <- liftIO $ Vec.getSize (svTrail solver)
      let h = CHTheory TheoryHandler
          callback l = assignBy solver l h
          loop i = do
            when (i < n) $ do
              l <- liftIO $ Vec.unsafeRead (svTrail solver) i
              ok <- liftIO $ thAssertLit t callback l
              if ok then
                loop (i+1)
              else
                throwE h
      loop =<< liftIO (readIOURef (svTheoryChecked solver))
      b2 <- liftIO $ thCheck t callback
      if b2 then do
        liftIO $ writeIOURef (svTheoryChecked solver) n
      else
        throwE h

data TheoryHandler = TheoryHandler deriving (Eq)

instance Hashable TheoryHandler where
  hash _ = hash ()
  hashWithSalt = defaultHashWithSalt

instance ConstraintHandler TheoryHandler where
  toConstraintHandler = CHTheory

  showConstraintHandler _this = return "TheoryHandler"

  constrAttach _solver _this _this2 = error "TheoryHandler.constrAttach"

  constrDetach _solver _this _this2 = return ()

  constrIsLocked _solver _this _this2 = return True

  constrPropagate _solver _this _this2 _falsifiedLit =  error "TheoryHandler.constrPropagate"

  constrReasonOf solver _this l = do
    Just t <- readIORef (svTheorySolver solver)
    lits <- thExplain t l
    return $ [-lit | lit <- lits]

  constrOnUnassigned _solver _this _this2 _lit = return ()

  isPBRepresentable _this = return False

  toPBLinAtLeast _this = error "TheoryHandler.toPBLinAtLeast"

  isSatisfied _solver _this = error "TheoryHandler.isSatisfied"

  constrIsProtected _solver _this = error "TheoryHandler.constrIsProtected"

  constrReadActivity _this = return 0

  constrWriteActivity _this _aval = return ()

{--------------------------------------------------------------------
  Restart strategy
--------------------------------------------------------------------}

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

shift :: IORef [a] -> IO a
shift ref = do
  (x:xs) <- readIORef ref
  writeIORef ref xs
  return x

defaultHashWithSalt :: Hashable a => Int -> a -> Int
defaultHashWithSalt salt x = salt `combine` hash x
  where
    combine :: Int -> Int -> Int
    combine h1 h2 = (h1 * 16777619) `xor` h2

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
      s <- showConstraintHandler c
      log solver $ "BUG: " ++ s ++ " is violated"

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
    s <- showConstraintHandler c
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
