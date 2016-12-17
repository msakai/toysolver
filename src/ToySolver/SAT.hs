{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
{-# LANGUAGE BangPatterns, ScopedTypeVariables, CPP, DeriveDataTypeable, RecursiveDo, MultiParamTypeClasses, InstanceSigs #-}
#ifdef __GLASGOW_HASKELL__
{-# LANGUAGE UnboxedTuples, MagicHash #-}
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

  -- * Extract results
  , IModel (..)
  , Model
  , getModel
  , getFailedAssumptions
  , getAssumptionsImplications

  -- * Solver configulation
  , Config (..)
  , getConfig
  , setConfig
  , modifyConfig
  , RestartStrategy (..)
  , showRestartStrategy
  , parseRestartStrategy
  , LearningStrategy (..)
  , showLearningStrategy
  , parseLearningStrategy
  , setVarPolarity
  , setLogger
  , setRandomGen
  , getRandomGen
  , setConfBudget
  , PBHandlerType (..)
  , showPBHandlerType
  , parsePBHandlerType

  -- ** Deprecated
  , setRestartStrategy
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
  , setLearningStrategy
  , setEnablePhaseSaving
  , getEnablePhaseSaving
  , defaultEnablePhaseSaving
  , setEnableForwardSubsumptionRemoval
  , getEnableForwardSubsumptionRemoval
  , defaultEnableForwardSubsumptionRemoval
  , setEnableBackwardSubsumptionRemoval
  , getEnableBackwardSubsumptionRemoval
  , defaultEnableBackwardSubsumptionRemoval
  , setCheckModel
  , setRandomFreq
  , defaultRandomFreq
  , setPBHandlerType
  , setPBSplitClausePart
  , getPBSplitClausePart
  , defaultPBSplitClausePart

  -- * Read state
  , getNVars
  , getNConstraints
  , getNLearntConstraints
  , getVarFixed
  , getLitFixed
  , getFixedLiterals

  -- * Read state (deprecated)
  , nVars
  , nAssigns
  , nConstraints
  , nLearnt  

  -- * Internal API
  , varBumpActivity
  , varDecayActivity
  ) where

import Prelude hiding (log)
import Control.Applicative hiding (empty)
import Control.Loop
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Except
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
import Data.Char
import Data.Default.Class
import Data.Either
import Data.Function (on)
import Data.Hashable
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.IORef
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
import ToySolver.SAT.Types
import ToySolver.SAT.TheorySolver
import ToySolver.Internal.Util (revMapM)

{--------------------------------------------------------------------
  internal data structures
--------------------------------------------------------------------}

type Level = Int

levelRoot :: Level
levelRoot = 0

data VarData
  = VarData
  { vdPolarity   :: !(IORef Bool)
  , vdPosLitData :: !LitData
  , vdNegLitData :: !LitData
  -- | will be invoked once when the variable is assigned
  , vdWatches    :: !(IORef [SomeConstraintHandler])
  , vdActivity   :: !(IOURef VarActivity)
  , vdValue :: !(IORef LBool)
  , vdTrailIndex :: !(IOURef Int)
  , vdLevel :: !(IOURef Level)
  , vdReason :: !(IORef (Maybe SomeConstraintHandler))
  , vdOnUnassigned :: !(IORef [SomeConstraintHandler])
  }

data LitData
  = LitData
  { -- | will be invoked when this literal is falsified
    ldWatches   :: !(IORef [SomeConstraintHandler])
  , ldOccurList :: !(IORef (HashSet SomeConstraintHandler))
  }

newVarData :: IO VarData
newVarData = do
  polarity <- newIORef True
  pos <- newLitData
  neg <- newLitData
  watches <- newIORef []
  activity <- newIOURef 0

  val <- newIORef lUndef
  idx <- newIOURef maxBound
  lv <- newIOURef maxBound
  reason <- newIORef Nothing
  onUnassigned <- newIORef []

  return $
    VarData
    { vdPolarity = polarity
    , vdPosLitData = pos
    , vdNegLitData = neg
    , vdWatches = watches
    , vdActivity = activity
    , vdValue = val
    , vdTrailIndex = idx
    , vdLevel = lv
    , vdReason = reason
    , vdOnUnassigned = onUnassigned
    }

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
  readIORef (vdValue vd)

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

getVarFixed :: Solver -> Var -> IO LBool
getVarFixed solver !v = do
  vd <- varData solver v
  lv <- readIOURef (vdLevel vd)
  if lv == levelRoot then
    readIORef (vdValue vd)
  else
    return lUndef

getLitFixed :: Solver -> Lit -> IO LBool
getLitFixed solver !l = do
  -- litVar による heap allocation を避けるために、
  -- litPolarityによる分岐後にvarDataを呼ぶ。
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
  vd <- varData solver v
  val <- readIORef (vdValue vd)
  when (val == lUndef) $ error ("ToySolver.SAT.varLevel: unassigned var " ++ show v)
  readIOURef (vdLevel vd)

litLevel :: Solver -> Lit -> IO Level
litLevel solver l = varLevel solver (litVar l)

varReason :: Solver -> Var -> IO (Maybe SomeConstraintHandler)
varReason solver !v = do
  vd <- varData solver v
  val <- readIORef (vdValue vd)
  when (val == lUndef) $ error ("ToySolver.SAT.varReason: unassigned var " ++ show v)
  readIORef (vdReason vd)

varAssignNo :: Solver -> Var -> IO Int
varAssignNo solver !v = do
  vd <- varData solver v
  val <- readIORef (vdValue vd)
  when (val == lUndef) $ error ("ToySolver.SAT.varAssignNo: unassigned var " ++ show v)
  readIOURef (vdTrailIndex vd)

-- | Solver instance
data Solver
  = Solver
  { svOk           :: !(IORef Bool)

  , svVarQueue     :: !PQ.PriorityQueue
  , svTrail        :: !(Vec.UVec Lit)
  , svTrailLimit   :: !(Vec.UVec Lit)
  , svTrailNPropagated :: !(IOURef Int)

  , svVarData      :: !(Vec.Vec VarData)
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
  , svAssumptions     :: !(Vec.UVec Lit)
  , svLearntLim       :: !(IORef Int)
  , svLearntLimAdjCnt :: !(IORef Int)
  , svLearntLimSeq    :: !(IORef [(Int,Int)])

  -- | Amount to bump next variable with.
  , svVarInc       :: !(IOURef Double)

  -- | Amount to bump next constraint with.
  , svConstrInc    :: !(IOURef Double)
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
  vd <- varData solver (litVar lit)
  let val = liftBool (litPolarity lit)

  val0 <- readIORef (vdValue vd)
  if val0 /= lUndef then do    
    return $ val == val0
  else do
    idx <- Vec.getSize (svTrail solver)
    lv <- getDecisionLevel solver

    writeIORef (vdValue vd) val
    writeIOURef (vdTrailIndex vd) idx
    writeIOURef (vdLevel vd) lv
    writeIORef (vdReason vd) reason

    Vec.push (svTrail solver) lit

    when debugMode $ logIO solver $ do
      let r = case reason of
                Nothing -> ""
                Just _ -> " by propagation"
      return $ printf "assign(level=%d): %d%s" lv lit r

    return True

unassign :: Solver -> Var -> IO ()
unassign solver !v = assert (validVar v) $ do
  vd <- varData solver v
  val <- readIORef (vdValue vd)
  when (val == lUndef) $ error "unassign: should not happen"

  flag <- getEnablePhaseSaving solver
  when flag $ writeIORef (vdPolarity vd) $! fromJust (unliftBool val)

  writeIORef (vdValue vd) lUndef
  writeIOURef (vdTrailIndex vd) maxBound
  writeIOURef (vdLevel vd) maxBound
  writeIORef (vdReason vd) Nothing

  let !l = if val == lTrue then v else -v
  cs <- readIORef (vdOnUnassigned vd)
  writeIORef (vdOnUnassigned vd) []
  forM_ cs $ \c ->
    constrOnUnassigned solver c c l

  PQ.enqueue (svVarQueue solver) v

addOnUnassigned :: Solver -> SomeConstraintHandler -> Lit -> IO ()
addOnUnassigned solver constr !l = do
  vd <- varData solver (litVar l)
  val <- readIORef (vdValue vd)
  when (val == lUndef) $ error "addOnUnassigned: should not happen"
  modifyIORef (vdOnUnassigned vd) (constr :)

-- | Register the constraint to be notified when the literal becames false.
watchLit :: Solver -> Lit -> SomeConstraintHandler -> IO ()
watchLit solver !lit c = do
  ld <- litData solver lit
  modifyIORef (ldWatches ld) (c : )

-- | Register the constraint to be notified when the variable is assigned.
watchVar :: Solver -> Var -> SomeConstraintHandler -> IO ()
watchVar solver !var c = do
  vd <- varData solver var
  modifyIORef (vdWatches vd) (c : )

unwatchLit :: Solver -> Lit -> SomeConstraintHandler -> IO ()
unwatchLit solver !lit c = do
  ld <- litData solver lit
  modifyIORef (ldWatches ld) (delete c)

unwatchVar :: Solver -> Lit -> SomeConstraintHandler -> IO ()
unwatchVar solver !lit c = do
  vd <- varData solver lit
  modifyIORef (vdWatches vd) (delete c)

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
       ld <- litData solver lit
       modifyIORef' (ldOccurList ld) (HashSet.insert c2)

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
varActivity solver !v = do
  vd <- varData solver v
  readIOURef (vdActivity vd)

varDecayActivity :: Solver -> IO ()
varDecayActivity solver = do
  d <- configVarDecay <$> getConfig solver
  modifyIOURef (svVarInc solver) (d*)

varBumpActivity :: Solver -> Var -> IO ()
varBumpActivity solver !v = do
  inc <- readIOURef (svVarInc solver)
  vd <- varData solver v
  modifyIOURef (vdActivity vd) (+inc)
  PQ.update (svVarQueue solver) v
  aval <- readIOURef (vdActivity vd)
  when (aval > 1e20) $
    -- Rescale
    varRescaleAllActivity solver

varRescaleAllActivity :: Solver -> IO ()
varRescaleAllActivity solver = do
  vs <- variables solver
  forM_ vs $ \v -> do
    vd <- varData solver v
    modifyIOURef (vdActivity vd) (* 1e-20)
  modifyIOURef (svVarInc solver) (* 1e-20)

variables :: Solver -> IO [Var]
variables solver = do
  n <- getNVars solver
  return [1 .. n]

-- | number of variables of the problem.
getNVars :: Solver -> IO Int
getNVars solver = Vec.getSize (svVarData solver)

{-# DEPRECATED nVars "Use getNVars instead" #-}
-- | number of variables of the problem.
nVars :: Solver -> IO Int
nVars = getNVars

-- | number of assigned 
getNAssigned :: Solver -> IO Int
getNAssigned solver = Vec.getSize (svTrail solver)

{-# DEPRECATED nAssigns "nAssigns is deprecated" #-}
-- | number of assigned variables.
nAssigns :: Solver -> IO Int
nAssigns = getNAssigned

-- | number of constraints.
getNConstraints :: Solver -> IO Int
getNConstraints solver = do
  xs <- readIORef (svConstrDB solver)
  return $ length xs

{-# DEPRECATED nConstraints "Use getNConstraints instead" #-}
-- | number of constraints.
nConstraints :: Solver -> IO Int
nConstraints = getNConstraints

-- | number of learnt constrints.
getNLearntConstraints :: Solver -> IO Int
getNLearntConstraints solver = do
  (n,_) <- readIORef (svLearntDB solver)
  return n

{-# DEPRECATED nLearnt "Use getNLearntConstraints instead" #-}
-- | number of learnt constrints.
nLearnt :: Solver -> IO Int
nLearnt = getNLearntConstraints

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
  vars <- Vec.new
  vqueue <- PQ.newPriorityQueueBy (ltVar solver)
  db  <- newIORef []
  db2 <- newIORef (0,[])
  as  <- Vec.new
  m   <- newIORef Nothing
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

  let solver =
        Solver
        { svOk = ok
        , svVarQueue   = vqueue
        , svTrail      = trail
        , svTrailLimit = trail_lim
        , svTrailNPropagated = trail_nprop
        , svVarData    = vars
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
        , svAssumptions     = as
        , svLearntLim       = learntLim
        , svLearntLimAdjCnt = learntLimAdjCnt
        , svLearntLimSeq    = learntLimSeq
        , svVarInc      = varInc
        , svConstrInc   = constrInc
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

instance NewVar IO Solver where
  newVar :: Solver -> IO Var
  newVar solver = do
    n <- Vec.getSize (svVarData solver)
    let v = n + 1
    vd <- newVarData
    Vec.push (svVarData solver) vd
    PQ.enqueue (svVarQueue solver) v
    return v

  newVars :: Solver -> Int -> IO [Var]
  newVars solver n = do
    nv <- getNVars solver
    resizeVarCapacity solver (nv+n)
    replicateM n (newVar solver)

  newVars_ :: Solver -> Int -> IO ()
  newVars_ solver n = do
    nv <- getNVars solver
    resizeVarCapacity solver (nv+n)
    replicateM_ n (newVar solver)

-- |Pre-allocate internal buffer for @n@ variables.
resizeVarCapacity :: Solver -> Int -> IO ()
resizeVarCapacity solver n = do
  Vec.resizeCapacity (svVarData solver) n
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
              b <- getPBSplitClausePart solver
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

    restartStrategy <- configRestartStrategy <$> getConfig solver
    restartFirst  <- configRestartFirst <$> getConfig solver
    restartInc    <- configRestartInc <$> getConfig solver
    unless (restartInc > 1) $ error "restartInc must be >1"
    let restartSeq =
          if restartFirst > 0
          then mkRestartSeq restartStrategy restartFirst restartInc
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
      learntSizeFirst <- configLearntSizeFirst <$> getConfig solver
      learntSizeInc   <- configLearntSizeInc <$> getConfig solver
      unless (learntSizeInc > 1) $ error "learntSizeInc must be >1"
      nc <- getNConstraints solver
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

    when (result == Just True) $ do
      when (configCheckModel config) $ checkSatisfied solver
      constructModel solver
      mt <- getTheory solver
      case mt of
        Nothing -> return ()
        Just t -> thConstructModel t
    unless (result == Just False) $ do
      saveAssumptionsImplications solver

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

      when (c `mod` 100 == 0) $ do
        printStat solver False

      if d == levelRoot then do
        markBad solver
        return $ Just (SRFinished False)
      else if confBudget==0 then
        return $ Just SRBudgetExceeded
      else if conflict_lim > 0 && c >= conflict_lim then
        return $ Just SRRestart
      else do
        strat <- configLearningStrategy <$> getConfig solver
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
          let constr = toConstraintHandler cl
          addToLearntDB solver constr
          basicAttachClauseHandler solver cl
          assignBy solver lit constr
          constrBumpActivity solver constr

    learnHybrid :: IORef Int -> SomeConstraintHandler -> IO (Maybe SearchResult)
    learnHybrid conflictCounter constr = do
      ((learntClause, clauseLevel), pb) <- analyzeConflictHybrid solver constr
      let minLevel =
            case pb of
              Nothing -> clauseLevel
              Just (_, pbLevel) -> min clauseLevel pbLevel
      backtrackTo solver minLevel

      case learntClause of
        [] -> error "search(LearningHybrid): should not happen"
        [lit] -> do
          _ <- assign solver lit -- This should always succeed.
          return ()
        lit:_ -> do
          cl <- newClauseHandler learntClause True
          let constr = toConstraintHandler cl
          addToLearntDB solver constr
          basicAttachClauseHandler solver cl
          constrBumpActivity solver constr
          when (minLevel == clauseLevel) $ do
            _ <- assignBy solver lit constr -- This should always succeed.
            return ()

      ret <- deduce solver
      case ret of
        Just conflicted -> do
          handleConflict conflictCounter conflicted
          -- TODO: should also learn the PB constraint?
        Nothing -> do
          case pb of
            Nothing -> return Nothing
            Just ((lhs,rhs), _pbLevel) -> do
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
  flag <- getEnableForwardSubsumptionRemoval solver
  if not flag then
    return False
  else do
    withEnablePhaseSaving solver False $ do
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
        s <- showConstraintHandler c
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
            pb2 <- instantiatePBLinAtLeast (getLitFixed solver) =<< toPBLinAtLeast c
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
  modifyIOURef (svNRemovedConstr solver) (+n)
  writeIORef (svConstrDB solver) ys

{--------------------------------------------------------------------
  Parameter settings.
--------------------------------------------------------------------}

{--------------------------------------------------------------------
  Configulation
--------------------------------------------------------------------}
         
data Config
  = Config
  { configRestartStrategy :: !RestartStrategy
  , configRestartFirst :: !Int
    -- ^ The initial restart limit. (default 100)
    -- Zero and negative values are used to disable restart.
  , configRestartInc :: !Double
    -- ^ The factor with which the restart limit is multiplied in each restart. (default 1.5)
    -- This must be @>1@.
  , configLearningStrategy :: !LearningStrategy
  , configLearntSizeFirst :: !Int
    -- ^ The initial limit for learnt constraints.
    -- Negative value means computing default value from problem instance.
  , configLearntSizeInc :: !Double
    -- ^ The limit for learnt constraints is multiplied with this factor periodically. (default 1.1)
    -- This must be @>1@.                     
  , configCCMin :: !Int
    -- ^ Controls conflict constraint minimization (0=none, 1=local, 2=recursive)
  , configEnablePhaseSaving :: !Bool
  , configEnableForwardSubsumptionRemoval :: !Bool
  , configEnableBackwardSubsumptionRemoval :: !Bool
  , configRandomFreq :: !Double
    -- ^ The frequency with which the decision heuristic tries to choose a random variable
  , configPBHandlerType :: !PBHandlerType
  , configEnablePBSplitClausePart :: !Bool
    -- ^ Split PB-constraints into a PB part and a clause part.
    --
    -- Example from minisat+ paper:
    --
    -- * 4 x1 + 4 x2 + 4 x3 + 4 x4 + 2y1 + y2 + y3 ≥ 4
    -- 
    -- would be split into
    --
    -- * x1 + x2 + x3 + x4 + ¬z ≥ 1 (clause part)
    --
    -- * 2 y1 + y2 + y3 + 4 z ≥ 4 (PB part)
    --
    -- where z is a newly introduced variable, not present in any other constraint.
    -- 
    -- Reference:
    -- 
    -- * N . Eéen and N. Sörensson. Translating Pseudo-Boolean Constraints into SAT. JSAT 2:1–26, 2006.
    --                               
  , configCheckModel :: !Bool
  , configVarDecay :: !Double
    -- ^ Inverse of the variable activity decay factor. (default 1 / 0.95)
  , configConstrDecay :: !Double
    -- ^ Inverse of the constraint activity decay factor. (1 / 0.999)
  } deriving (Show, Eq, Ord)

instance Default Config where
  def =
    Config
    { configRestartStrategy = def
    , configRestartFirst = defaultRestartFirst
    , configRestartInc = defaultRestartInc
    , configLearningStrategy = def
    , configLearntSizeFirst = defaultLearntSizeFirst
    , configLearntSizeInc = defaultLearntSizeInc
    , configCCMin = defaultCCMin
    , configEnablePhaseSaving = defaultEnablePhaseSaving
    , configEnableForwardSubsumptionRemoval = defaultEnableForwardSubsumptionRemoval
    , configEnableBackwardSubsumptionRemoval = defaultEnableBackwardSubsumptionRemoval
    , configRandomFreq = defaultRandomFreq
    , configPBHandlerType = def
    , configEnablePBSplitClausePart = defaultPBSplitClausePart
    , configCheckModel = False
    , configVarDecay = 1 / 0.95
    , configConstrDecay = 1 / 0.999
    }

getConfig :: Solver -> IO Config
getConfig solver = readIORef $ svConfig solver

setConfig :: Solver -> Config -> IO ()
setConfig solver = writeIORef (svConfig solver)

modifyConfig :: Solver -> (Config -> Config) -> IO ()
modifyConfig solver = modifyIORef' (svConfig solver)

{-# DEPRECATED setRestartStrategy "Use setConfig" #-}
setRestartStrategy :: Solver -> RestartStrategy -> IO ()
setRestartStrategy solver s = modifyIORef' (svConfig solver) $ \config -> config{ configRestartStrategy = s }

-- | The initial restart limit. (default 100)
-- Zero and negative values are used to disable restart.
{-# DEPRECATED setRestartFirst "Use setConfig" #-}
setRestartFirst :: Solver -> Int -> IO ()
setRestartFirst solver !n = modifyIORef' (svConfig solver) $ \config -> config{ configRestartFirst = n }

-- | default value for @RestartFirst@.
{-# DEPRECATED defaultRestartFirst "Use configRestartFirst def" #-}
defaultRestartFirst :: Int
defaultRestartFirst = 100

-- | The factor with which the restart limit is multiplied in each restart. (default 1.5)
-- 
-- This must be @>1@.
{-# DEPRECATED setRestartInc "Use setConfig" #-}
setRestartInc :: Solver -> Double -> IO ()
setRestartInc solver !r
  | r > 1 = modifyIORef' (svConfig solver) $ \config -> config{ configRestartInc = r }
  | otherwise = error "setRestartInc: RestartInc must be >1"

-- | default value for @RestartInc@.
{-# DEPRECATED defaultRestartInc "Use configRestartInc def" #-}
defaultRestartInc :: Double
defaultRestartInc = 1.5

-- | Learning strategy.
--
-- The default value can be obtained by 'def'.
data LearningStrategy
  = LearningClause
  | LearningHybrid
  deriving (Show, Eq, Ord, Enum, Bounded)

instance Default LearningStrategy where
  def = LearningClause

showLearningStrategy :: LearningStrategy -> String
showLearningStrategy LearningClause = "clause"
showLearningStrategy LearningHybrid = "hybrid"

parseLearningStrategy :: String -> Maybe LearningStrategy
parseLearningStrategy s =
  case map toLower s of
    "clause" -> Just LearningClause
    "hybrid" -> Just LearningHybrid
    _ -> Nothing

{-# DEPRECATED setLearningStrategy "Use setConfig" #-}
setLearningStrategy :: Solver -> LearningStrategy -> IO ()
setLearningStrategy solver l = modifyIORef' (svConfig solver) $ \config -> config{ configLearningStrategy = l }

-- | The initial limit for learnt clauses.
-- 
-- Negative value means computing default value from problem instance.
{-# DEPRECATED setLearntSizeFirst "Use setConfig" #-}
setLearntSizeFirst :: Solver -> Int -> IO ()
setLearntSizeFirst solver !x = modifyIORef' (svConfig solver) $ \config -> config{ configLearntSizeFirst = x }

-- | default value for @LearntSizeFirst@.
{-# DEPRECATED defaultLearntSizeFirst "Use learntSizeFirst def" #-}
defaultLearntSizeFirst :: Int
defaultLearntSizeFirst = -1

-- | The limit for learnt clauses is multiplied with this factor each restart. (default 1.1)
-- 
-- This must be @>1@.
{-# DEPRECATED setLearntSizeInc "Use setConfig" #-}
setLearntSizeInc :: Solver -> Double -> IO ()
setLearntSizeInc solver !r
  | r > 1 = modifyIORef' (svConfig solver) $ \config -> config{ configLearntSizeInc = r }
  | otherwise = error "setLearntSizeInc: LearntSizeInc must be >1"

-- | default value for @LearntSizeInc@.
{-# DEPRECATED defaultLearntSizeInc "Use learntSizeInc def" #-}
defaultLearntSizeInc :: Double
defaultLearntSizeInc = 1.1

-- | Controls conflict clause minimization (0=none, 1=basic, 2=deep)
{-# DEPRECATED setCCMin "Use setConfig" #-}
setCCMin :: Solver -> Int -> IO ()
setCCMin solver !v = modifyIORef' (svConfig solver) $ \config -> config{ configCCMin = v }

-- | default value for @CCMin@.
{-# DEPRECATED defaultCCMin "Use ccMin def" #-}
defaultCCMin :: Int
defaultCCMin = 2

-- | The default polarity of a variable.
setVarPolarity :: Solver -> Var -> Bool -> IO ()
setVarPolarity solver v val = do
  vd <- varData solver v
  writeIORef (vdPolarity vd) val

{-# DEPRECATED setCheckModel "Use setConfig" #-}
setCheckModel :: Solver -> Bool -> IO ()
setCheckModel solver flag = do
  modifyIORef' (svConfig solver) $ \config -> config{ configCheckModel = flag }

-- | The frequency with which the decision heuristic tries to choose a random variable
{-# DEPRECATED setRandomFreq "Use setConfig" #-}
setRandomFreq :: Solver -> Double -> IO ()
setRandomFreq solver r =
  modifyIORef' (svConfig solver) $ \config -> config{ configRandomFreq = r }

{-# DEPRECATED defaultRandomFreq "Use configRandomFreq def" #-}
defaultRandomFreq :: Double
defaultRandomFreq = 0.005

-- | Set random generator used by the random variable selection
setRandomGen :: Solver -> Rand.GenIO -> IO ()
setRandomGen solver = writeIORef (svRandomGen solver)

-- | Get random generator used by the random variable selection
getRandomGen :: Solver -> IO Rand.GenIO
getRandomGen solver = readIORef (svRandomGen solver)

setConfBudget :: Solver -> Maybe Int -> IO ()
setConfBudget solver (Just b) | b >= 0 = writeIOURef (svConfBudget solver) b
setConfBudget solver _ = writeIOURef (svConfBudget solver) (-1)

-- | Pseudo boolean constraint handler implimentation.
--
-- The default value can be obtained by 'def'.
data PBHandlerType = PBHandlerTypeCounter | PBHandlerTypePueblo
  deriving (Show, Eq, Ord, Enum, Bounded)

instance Default PBHandlerType where
  def = PBHandlerTypeCounter

showPBHandlerType :: PBHandlerType -> String
showPBHandlerType PBHandlerTypeCounter = "counter"
showPBHandlerType PBHandlerTypePueblo = "pueblo"

parsePBHandlerType :: String -> Maybe PBHandlerType
parsePBHandlerType s =
  case map toLower s of
    "counter" -> Just PBHandlerTypeCounter
    "pueblo" -> Just PBHandlerTypePueblo
    _ -> Nothing

{-# DEPRECATED setPBHandlerType "Use setConfig" #-}
setPBHandlerType :: Solver -> PBHandlerType -> IO ()
setPBHandlerType solver ht = do
  modifyIORef' (svConfig solver) $ \config -> config{ configPBHandlerType = ht }

-- | Split PB-constraints into a PB part and a clause part.
--
-- Example from minisat+ paper:
--
-- * 4 x1 + 4 x2 + 4 x3 + 4 x4 + 2y1 + y2 + y3 ≥ 4
-- 
-- would be split into
--
-- * x1 + x2 + x3 + x4 + ¬z ≥ 1 (clause part)
--
-- * 2 y1 + y2 + y3 + 4 z ≥ 4 (PB part)
--
-- where z is a newly introduced variable, not present in any other constraint.
-- 
-- Reference:
-- 
-- * N. Eén and N. Sörensson. Translating Pseudo-Boolean Constraints into SAT. JSAT 2:1–26, 2006.
--
{-# DEPRECATED setPBSplitClausePart "Use setConfig" #-}
setPBSplitClausePart :: Solver -> Bool -> IO ()
setPBSplitClausePart solver b =
  modifyIORef' (svConfig solver) $ \config -> config{ configEnablePBSplitClausePart = b }

-- | See documentation of 'setPBSplitClausePart'.
getPBSplitClausePart :: Solver -> IO Bool
getPBSplitClausePart solver =
  configEnablePBSplitClausePart <$> getConfig solver

-- | See documentation of 'setPBSplitClausePart'.
{-# DEPRECATED defaultPBSplitClausePart "Use configEnablePBSplitClausePart def" #-}
defaultPBSplitClausePart :: Bool
defaultPBSplitClausePart = False

{-# DEPRECATED setEnablePhaseSaving "Use setConfig" #-}
setEnablePhaseSaving :: Solver -> Bool -> IO ()
setEnablePhaseSaving solver flag = do
  modifyIORef' (svConfig solver) $ \config -> config{ configEnablePhaseSaving = flag }

{-# DEPRECATED getEnablePhaseSaving "Use getConfig" #-}
getEnablePhaseSaving :: Solver -> IO Bool
getEnablePhaseSaving solver = do
  configEnablePhaseSaving <$> getConfig solver

{-# DEPRECATED defaultEnablePhaseSaving "Use configEnablePhaseSaving def" #-}
defaultEnablePhaseSaving :: Bool
defaultEnablePhaseSaving = True

{-# DEPRECATED setEnableForwardSubsumptionRemoval "Use setConfig" #-}
setEnableForwardSubsumptionRemoval :: Solver -> Bool -> IO ()
setEnableForwardSubsumptionRemoval solver flag = do
  modifyIORef' (svConfig solver) $ \config -> config{ configEnableForwardSubsumptionRemoval = flag }

{-# DEPRECATED getEnableForwardSubsumptionRemoval "Use getConfig" #-}
getEnableForwardSubsumptionRemoval :: Solver -> IO Bool
getEnableForwardSubsumptionRemoval solver = do
  configEnableForwardSubsumptionRemoval <$> getConfig solver

{-# DEPRECATED defaultEnableForwardSubsumptionRemoval "Use configEnableForwardSubsumptionRemoval def" #-}
defaultEnableForwardSubsumptionRemoval :: Bool
defaultEnableForwardSubsumptionRemoval = False

{-# DEPRECATED setEnableBackwardSubsumptionRemoval "Use setConfig" #-}
setEnableBackwardSubsumptionRemoval :: Solver -> Bool -> IO ()
setEnableBackwardSubsumptionRemoval solver flag = do
  modifyIORef' (svConfig solver) $ \config -> config{ configEnableBackwardSubsumptionRemoval = flag }

{-# DEPRECATED getEnableBackwardSubsumptionRemoval "Use getConfig" #-}
getEnableBackwardSubsumptionRemoval :: Solver -> IO Bool
getEnableBackwardSubsumptionRemoval solver = do
  configEnableBackwardSubsumptionRemoval <$> getConfig solver

{-# DEPRECATED defaultEnableBackwardSubsumptionRemoval "Use configEnableBackwardSubsumptionRemoval def" #-}
defaultEnableBackwardSubsumptionRemoval :: Bool
defaultEnableBackwardSubsumptionRemoval = False

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
    vd <- varData solver var2
    -- TODO: random polarity
    p <- readIORef (vdPolarity vd)
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
deduce solver = do
  m <- deduceB solver
  case m of
    Just _ -> return m
    Nothing -> do
      m2 <- deduceT solver
      case m2 of
        Just _ -> return m2
        Nothing -> do
          empty <- bcpIsEmpty solver
          if empty then
            return Nothing
          else
            deduce solver

deduceB :: Solver -> IO (Maybe SomeConstraintHandler)
deduceB solver = loop
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
              ret <- processVar lit
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
  d <- getDecisionLevel solver

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
            l <- peekTrail solver
            if litNot l `IS.notMember` lits1 then do
              popTrail solver
              loop lits1 lits2
            else do
              m <- varReason solver (litVar l)
              case m of
                Nothing -> error "analyzeConflict: should not happen"
                Just constr2 -> do
                  constrBumpActivity solver constr2
                  xs <- reasonOf solver constr2 (Just l)
                  forM_ xs $ \lit -> varBumpActivity solver (litVar lit)
                  popTrail solver
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

analyzeConflictHybrid :: ConstraintHandler c => Solver -> c -> IO ((Clause, Level), Maybe (PBLinAtLeast, Level))
analyzeConflictHybrid solver constr = do
  d <- getDecisionLevel solver

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
            l <- peekTrail solver
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
                           b <- isPBRepresentable constr2
                           if not b then do
                             return $ clauseToPBLinAtLeast (l:xs)
                           else do
                             pb2 <- toPBLinAtLeast constr2
                             o <- pbOverSAT solver pb2
                             if o then
                               return $ clauseToPBLinAtLeast (l:xs)
                             else
                               return pb2
                         return $ cutResolve pb pb2 (litVar l)
                       else return pb

                popTrail solver
                loop lits1' lits2' pb'

        | otherwise = error "analyzeConflictHybrid: should not happen: reason of current level is empty"
        where
          sz = IS.size lits1

  constrBumpActivity solver constr
  conflictClause <- reasonOf solver constr Nothing
  pbConfl <- do
    b <- isPBRepresentable constr
    if b then
      toPBLinAtLeast constr
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

  case pbToClause pb of
    Nothing -> do  
      pblevel <- pbBacktrackLevel solver pb
      return ((map fst xs, level), Just (pb, pblevel))
    Just _ -> do
      return ((map fst xs, level), Nothing)

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
    vd <- varData solver v
    val <- readIORef (vdValue vd)
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
      ld <- litData solver lit
      modifyIORef' (ldOccurList ld) (HashSet.delete c)

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

-- To avoid heap-allocating Maybe value, it returns -1 when not found.
findForWatch2 :: Solver -> IOUArray Int Lit -> Int -> Int -> IO Int
#ifndef __GLASGOW_HASKELL__
findForWatch2 solver a beg end = go beg end
  where
    go :: Int -> Int -> IO Int
    go i end | i > end = return (-1)
    go i end = do
      val <- litValue s =<< unsafeRead a i
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
#if __GLASGOW_HASKELL__ < 708
    go# i end w | i ># end = (# w, -1# #)
#else
    go# i end w | isTrue# (i ># end) = (# w, -1# #)
#endif
    go# i end w =
      case unIO (litValue solver =<< unsafeRead a (I# i)) w of
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
  { claLits :: !(IOUArray Int Lit)
  , claActivity :: !(IORef Double)
  , claHash :: !Int
  }

claGetSize :: ClauseHandler -> IO Int
claGetSize cla = do
  (lb,ub) <- getBounds (claLits cla)
  assert (lb == 0) $ return ()
  return $! ub-lb+1

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

  showConstraintHandler this = do
    lits <- getElems (claLits this)
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
      lit0 <- unsafeRead (claLits this2) 0
      assignBy solver lit0 this
    else do
      ref <- newIORef 1
      let f i = do
            lit_i <- unsafeRead (claLits this2) i
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
                  lit_k <- unsafeRead (claLits this2) k
                  unsafeWrite (claLits this2) i lit_k
                  unsafeWrite (claLits this2) k lit_i
                  writeIORef ref $! (k+1)
                  return True

      b <- f 0
      if b then do
        lit0 <- unsafeRead (claLits this2) 0
        watchLit solver lit0 this
        b2 <- f 1
        if b2 then do
          lit1 <- unsafeRead (claLits this2) 1
          watchLit solver lit1 this
          return True
        else do -- UNIT
          -- We need to watch the most recently falsified literal
          (i,_) <- liftM (maximumBy (comparing snd)) $ forM [1..size-1] $ \l -> do
            lit <- unsafeRead (claLits this2) l
            lv <- litLevel solver lit
            return (l,lv)
          lit1 <- unsafeRead (claLits this2) 1
          liti <- unsafeRead (claLits this2) i
          unsafeWrite (claLits this2) 1 liti
          unsafeWrite (claLits this2) i lit1
          watchLit solver liti this
          assignBy solver lit0 this -- should always succeed
      else do -- CONFLICT
        ls <- liftM (map fst . sortBy (flip (comparing snd))) $ forM [0..size-1] $ \l -> do
          lit <- unsafeRead (claLits this2) l
          lv <- litLevel solver lit
          return (l,lv)
        forM_ (zip [0..] ls) $ \(i,lit) -> do
          unsafeWrite (claLits this2) i lit
        lit0 <- unsafeRead (claLits this2) 0
        lit1 <- unsafeRead (claLits this2) 1
        watchLit solver lit0 this
        watchLit solver lit1 this
        return False

  constrDetach solver this this2 = do
    size <- claGetSize this2
    when (size >= 2) $ do
      lit0 <- unsafeRead (claLits this2) 0
      lit1 <- unsafeRead (claLits this2) 1
      unwatchLit solver lit0 this
      unwatchLit solver lit1 this

  constrIsLocked solver this this2 = do
    size <- claGetSize this2
    if size < 2 then
      return False
    else do
      lit <- unsafeRead (claLits this2) 0
      isReasonOf solver this lit

  constrPropagate !solver this this2 !falsifiedLit = do
    preprocess

    !lit0 <- unsafeRead a 0
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
          !lit1 <- unsafeRead a 1
          !liti <- unsafeRead a i
          unsafeWrite a 1 liti
          unsafeWrite a i lit1
          watchLit solver liti this
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

  constrReasonOf _ this l = do
    lits <- getElems (claLits this)
    case l of
      Nothing -> return lits
      Just lit -> do
        assert (lit == head lits) $ return ()
        return $ tail lits

  constrOnUnassigned _solver _this _this2 _lit = return ()

  isPBRepresentable _ = return True

  toPBLinAtLeast this = do
    lits <- getElems (claLits this)
    return ([(1,l) | l <- lits], 1)

  isSatisfied solver this = do
    (lb,ub) <- getBounds (claLits this)
    liftM isLeft $ runExceptT $ numLoop lb ub $ \i -> do
      v <- lift $ litValue solver =<< unsafeRead (claLits this) i
      when (v == lTrue) $ throwE ()

  constrIsProtected _ this = do
    size <- claGetSize this
    return $! size <= 2

  constrReadActivity this = readIORef (claActivity this)

  constrWriteActivity this aval = writeIORef (claActivity this) $! aval

basicAttachClauseHandler :: Solver -> ClauseHandler -> IO Bool
basicAttachClauseHandler solver this = do
  let constr = toConstraintHandler this
  lits <- getElems (claLits this)
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

  showConstraintHandler this = do
    lits <- getElems (atLeastLits this)
    return $ show lits ++ " >= " ++ show (atLeastNum this)

  -- FIXME: simplify implementation
  constrAttach solver this this2 = do
    -- BCP Queue should be empty at this point.
    -- If not, duplicated propagation happens.
    bcpCheckEmpty solver

    let a = atLeastLits this2
    (lb,ub) <- getBounds a
    assert (lb == 0) $ return ()
    let m = ub - lb + 1
        n = atLeastNum this2

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
                  watchLit solver lit_k this
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
                  watchLit solver lit_l this
                  -- n+1 literals (0 .. n) are watched.
                return True
            | otherwise = do
                assert (i < n && n <= j) $ return ()
                lit_i <- unsafeRead a i
                val_i <- litValue solver lit_i
                if val_i /= lFalse then do
                  watchLit solver lit_i this
                  f (i+1) j
                else do
                  k <- findForWatch solver a j ub
                  if k /= -1 then do
                    lit_k <- unsafeRead a k
                    unsafeWrite a i lit_k
                    unsafeWrite a k lit_i
                    watchLit solver lit_k this
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
                      watchLit solver lit_l this
                    -- n+1 literals (0 .. n) are watched.
                    return False
      f 0 n

  constrDetach solver this this2 = do
    lits <- getElems (atLeastLits this2)
    let n = atLeastNum this2
    when (length lits > n) $ do
      forLoop 0 (<=n) (+1) $ \i -> do
        lit <- unsafeRead (atLeastLits this2) i
        unwatchLit solver lit this

  constrIsLocked solver this this2 = do
    (lb,ub) <- getBounds (atLeastLits this2)
    let size = ub - lb + 1
        n = atLeastNum this2
        loop i
          | i > n = return False
          | otherwise = do
              l <- unsafeRead (atLeastLits this2) i
              b <- isReasonOf solver this l
              if b then return True else loop (i+1)
    if size >= n+1 then
      loop 0
    else
      return False

  constrPropagate solver this this2 falsifiedLit = do
    preprocess

    when debugMode $ do
      litn <- readArray a n
      unless (litn == falsifiedLit) $ error "AtLeastHandler.constrPropagate: should not happen"

    (lb,ub) <- getBounds a
    assert (lb==0) $ return ()
    i <- findForWatch solver a (n+1) ub
    case i of
      -1 -> do
        when debugMode $ logIO solver $ do
          str <- showConstraintHandler this
          return $ printf "constrPropagate: %s is unit" str
        watchLit solver falsifiedLit this
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
              li <- unsafeRead a i
              if (li /= falsifiedLit) then
                loop (i+1)
              else do
                ln <- unsafeRead a n
                unsafeWrite a n li
                unsafeWrite a i ln

  constrReasonOf solver this concl = do
    (lb,ub) <- getBounds (atLeastLits this)
    assert (lb==0) $ return ()
    let n = atLeastNum this
    falsifiedLits <- mapM (readArray (atLeastLits this)) [n..ub] -- drop first n elements
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
            error $ printf "AtLeastHandler.constrReasonOf: cannot find %d in first %d elements" n
        return falsifiedLits

  constrOnUnassigned _solver _this _this2 _lit = return ()

  isPBRepresentable _ = return True

  toPBLinAtLeast this = do
    lits <- getElems (atLeastLits this)
    return ([(1,l) | l <- lits], fromIntegral (atLeastNum this))

  isSatisfied solver this = do
    (lb,ub) <- getBounds (atLeastLits this)
    liftM isLeft $ runExceptT $ numLoopState lb ub 0 $ \(!n) i -> do
      v <- lift $ litValue solver =<< unsafeRead (atLeastLits this) i
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
  lits <- getElems (atLeastLits this)
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
          watchsum <- puebloGetWatchSum this
          if watchsum - c >= puebloDegree this then
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
  { xorLits :: !(IOUArray Int Lit)
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
  let size = length ls
  a <- newListArray (0, size-1) ls
  act <- newIORef $! (if learnt then 0 else -1)
  return (XORClauseHandler a act (hash ls))

instance ConstraintHandler XORClauseHandler where
  toConstraintHandler = CHXORClause

  showConstraintHandler this = do
    lits <- getElems (xorLits this)
    return ("XOR " ++ show lits)

  constrAttach solver this this2 = do
    -- BCP Queue should be empty at this point.
    -- If not, duplicated propagation happens.
    bcpCheckEmpty solver

    let a = xorLits this2
    (lb,ub) <- getBounds a
    assert (lb == 0) $ return ()
    let size = ub-lb+1

    if size == 0 then do
      markBad solver
      return False
    else if size == 1 then do
      lit0 <- unsafeRead a 0
      assignBy solver lit0 this
    else do
      ref <- newIORef 1
      let f i = do
            lit_i <- unsafeRead a i
            val_i <- litValue solver lit_i
            if val_i == lUndef then
              return True
            else do
              j <- readIORef ref
              k <- findForWatch2 solver a j ub
              case k of
                -1 -> do
                  return False
                _ -> do
                  lit_k <- unsafeRead a k
                  unsafeWrite a i lit_k
                  unsafeWrite a k lit_i
                  writeIORef ref $! (k+1)
                  return True

      b <- f 0
      if b then do
        lit0 <- unsafeRead a 0
        watchVar solver (litVar lit0) this
        b2 <- f 1
        if b2 then do
          lit1 <- unsafeRead a 1
          watchVar solver (litVar lit1) this
          return True
        else do -- UNIT
          -- We need to watch the most recently falsified literal
          (i,_) <- liftM (maximumBy (comparing snd)) $ forM [1..ub] $ \l -> do
            lit <- unsafeRead a l
            lv <- litLevel solver lit
            return (l,lv)
          lit1 <- unsafeRead a 1
          liti <- unsafeRead a i
          unsafeWrite a 1 liti
          unsafeWrite a i lit1
          watchVar solver (litVar liti) this
          -- lit0 ⊕ y
          y <- do
            ref <- newIORef False
            forLoop 1 (<=ub) (+1) $ \j -> do
              lit_j <- unsafeRead a j
              val_j <- litValue solver lit_j
              modifyIORef' ref (/= fromJust (unliftBool val_j))
            readIORef ref
          assignBy solver (if y then litNot lit0 else lit0) this -- should always succeed
      else do
        ls <- liftM (map fst . sortBy (flip (comparing snd))) $ forM [lb..ub] $ \l -> do
          lit <- unsafeRead a l
          lv <- litLevel solver lit
          return (l,lv)
        forM_ (zip [0..] ls) $ \(i,lit) -> do
          unsafeWrite a i lit
        lit0 <- unsafeRead a 0
        lit1 <- unsafeRead a 1
        watchVar solver (litVar lit0) this
        watchVar solver (litVar lit1) this
        isSatisfied solver this2

  constrDetach solver this this2 = do
    (lb,ub) <- getBounds (xorLits this2)
    let size = ub-lb+1
    when (size >= 2) $ do
      lit0 <- unsafeRead (xorLits this2) 0
      lit1 <- unsafeRead (xorLits this2) 1
      unwatchVar solver (litVar lit0) this
      unwatchVar solver (litVar lit1) this

  constrIsLocked solver this this2 = do
    lit0 <- unsafeRead (xorLits this2) 0
    lit1 <- unsafeRead (xorLits this2) 1
    b0 <- isReasonOf solver this lit0
    b1 <- isReasonOf solver this lit1
    return $ b0 || b1

  constrPropagate !solver this this2 !falsifiedLit = do
    b <- constrIsLocked solver this this2
    if b then
      return True
    else do
      preprocess
  
      !lit0 <- unsafeRead a 0
      (!lb,!ub) <- getBounds a
      assert (lb==0) $ return ()
      i <- findForWatch2 solver a 2 ub
      case i of
        -1 -> do
          when debugMode $ logIO solver $ do
             str <- showConstraintHandler this
             return $ printf "constrPropagate: %s is unit" str
          watchVar solver v this
          -- lit0 ⊕ y
          y <- do
            ref <- newIORef False
            forLoop 1 (<=ub) (+1) $ \j -> do
              lit_j <- unsafeRead a j
              val_j <- litValue solver lit_j
              modifyIORef' ref (/= fromJust (unliftBool val_j))
            readIORef ref
          assignBy solver (if y then litNot lit0 else lit0) this
        _  -> do
          !lit1 <- unsafeRead a 1
          !liti <- unsafeRead a i
          unsafeWrite a 1 liti
          unsafeWrite a i lit1
          watchVar solver (litVar liti) this
          return True

    where
      v = litVar falsifiedLit
      a = xorLits this2

      preprocess :: IO ()
      preprocess = do
        !l0 <- unsafeRead a 0
        !l1 <- unsafeRead a 1
        assert (litVar l0 == v || litVar l1 == v) $ return ()
        when (litVar l0 == v) $ do
          unsafeWrite a 0 l1
          unsafeWrite a 1 l0

  constrReasonOf solver this l = do
    lits <- getElems (xorLits this)
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
    lits <- getElems (xorLits this)
    vals <- mapM (litValue solver) lits
    let f x y
          | x == lUndef || y == lUndef = lUndef
          | otherwise = liftBool (x /= y)
    return $ foldl' f lFalse vals == lTrue

  constrIsProtected _ this = do
    size <- liftM rangeSize (getBounds (xorLits this))
    return $! size <= 2

  constrReadActivity this = readIORef (xorActivity this)

  constrWriteActivity this aval = writeIORef (xorActivity this) $! aval

basicAttachXORClauseHandler :: Solver -> XORClauseHandler -> IO Bool
basicAttachXORClauseHandler solver this = do
  lits <- getElems (xorLits this)
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

deduceT :: Solver -> IO (Maybe SomeConstraintHandler)
deduceT solver = do
  mt <- readIORef (svTheorySolver solver)
  case mt of
    Nothing -> return Nothing
    Just t -> do
      n <- Vec.getSize (svTrail solver)
      let h = CHTheory TheoryHandler
          callback l = assignBy solver l h
          loop i = do
            if i < n then do
              l <- Vec.unsafeRead (svTrail solver) i
              ok <- thAssertLit t callback l
              if ok then
                loop (i+1)
              else
                return False
            else do
              return True
      b <- loop =<< readIOURef (svTheoryChecked solver)
      if not b then
        return (Just h)
      else do
        b2 <- thCheck t callback
        if b2 then do
          writeIOURef (svTheoryChecked solver) n
          return Nothing
        else
          return (Just h)

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

-- | Restart strategy.
--
-- The default value can be obtained by 'def'.
data RestartStrategy = MiniSATRestarts | ArminRestarts | LubyRestarts
  deriving (Show, Eq, Ord, Enum, Bounded)

instance Default RestartStrategy where
  def = MiniSATRestarts

showRestartStrategy :: RestartStrategy -> String
showRestartStrategy MiniSATRestarts = "minisat"
showRestartStrategy ArminRestarts = "armin"
showRestartStrategy LubyRestarts = "luby"

parseRestartStrategy :: String -> Maybe RestartStrategy
parseRestartStrategy s =
  case map toLower s of
    "minisat" -> Just MiniSATRestarts
    "armin" -> Just ArminRestarts
    "luby" -> Just LubyRestarts
    _ -> Nothing

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
