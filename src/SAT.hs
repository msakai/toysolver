{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
{-# LANGUAGE BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  SAT
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (BangPatterns)
--
-- A CDCL SAT solver.
--
-- It follows design of MiniSat and SAT4J.
--
-----------------------------------------------------------------------------
module SAT
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
  , addClause
  , addAtLeast
  , addAtMost
  , addExactly
  , addPBAtLeast
  , addPBAtMost
  , addPBExactly

  -- * Solving
  , solve
  , solveWith

  -- * Extract results
  , Model
  , model

  -- * Solver configulation
  , setRestartFirst
  , defaultRestartFirst
  , setRestartInc
  , defaultRestartInc
  , setLearntSizeInc
  , defaultLearntSizeInc
  , setCCMin
  , defaultCCMin
  , setVarPolarity
  , setLogger

  -- * Read state
  , nVars
  , nAssigns
  , nClauses
  , nLearnt

  -- * Internal API
  , normalizePBAtLeast
  , varBumpActivity
  , varDecayActivity
  ) where

import Prelude hiding (log)
import Control.Monad
import Control.Exception
import Data.Array.IO
import Data.Array.Base (unsafeRead, unsafeWrite)
import Data.Function
import Data.IORef
import Data.List
import Data.Maybe
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Set as Set
import qualified Data.Sequence as Seq
import qualified PriorityQueue as PQ
import System.CPUTime
import Text.Printf
import LBool

{--------------------------------------------------------------------
  pure/persistent data structures
--------------------------------------------------------------------}

-- | Variable is represented as positive integers (DIMACS format).
type Var = Int

type VarMap = IM.IntMap

validVar :: Var -> Bool
validVar v = v > 0

-- | Positive (resp. negative) literals are represented as positive (resp.
-- negative) integers. (DIMACS format).
type Lit = Int

litUndef :: Lit
litUndef = 0

type LitSet = IS.IntSet
type LitMap = IM.IntMap

validLit :: Lit -> Bool
validLit l = l /= 0

-- | Construct a literal from a variable and its polarity.
-- 'True' (resp 'False') means positive (resp. negative) literal.
literal :: Var  -- ^ variable
        -> Bool -- ^ polarity
        -> Lit
literal v polarity =
  assert (validVar v) $ if polarity then v else litNot v

-- | Negation of the 'Lit'.
litNot :: Lit -> Lit
litNot l = assert (validLit l) $ negate l

{-# INLINE litVar #-}
-- | Underlying variable of the 'Lit'
litVar :: Lit -> Var
litVar l = assert (validLit l) $ abs l

{-# INLINE litPolarity #-}
-- | Polarity of the 'Lit'.
-- 'True' means positive literal and 'False' means negative literal.
litPolarity :: Lit -> Bool
litPolarity l = assert (validLit l) $ l > 0

-- | Disjunction of 'Lit'.
type Clause = [Lit]

-- | Normalizing clause
--
-- 'Nothing' if the clause is trivially true.
normalizeClause :: Clause -> Maybe Clause
normalizeClause lits = assert (IS.size ys `mod` 2 == 0) $
  if IS.null ys
    then Just (IS.toList xs)
    else Nothing
  where
    xs = IS.fromList lits
    ys = xs `IS.intersection` (IS.map litNot xs)

normalizeAtLeast :: ([Lit],Int) -> ([Lit],Int)
normalizeAtLeast (lits,n) = assert (IS.size ys `mod` 2 == 0) $
   (IS.toList lits', n')
   where
     xs = IS.fromList lits
     ys = xs `IS.intersection` (IS.map litNot xs)
     lits' = xs `IS.difference` ys
     n' = n - (IS.size ys `div` 2)

-- | normalizing PB constraint of the form /c1 x1 + c2 cn ... cn xn >= b/.
normalizePBAtLeast :: ([(Integer,Lit)], Integer) -> ([(Integer,Lit)], Integer)
normalizePBAtLeast a =
　case step2 $ step1 $ a of
    (xs,n)
      | n > 0     -> step3 (saturate n xs, n)
      | otherwise -> ([], 0) -- trivially true
  where
    -- 同じ変数が複数回現れないように、一度全部 @v@ に統一。
    step1 :: ([(Integer,Lit)], Integer) -> ([(Integer,Lit)], Integer)
    step1 (xs,n) =
      case loop (IM.empty,n) xs of
        (ys,n') -> ([(c,v) | (v,c) <- IM.toList ys], n')
      where
        loop :: (VarMap Integer, Integer) -> [(Integer,Lit)] -> (VarMap Integer, Integer)
        loop (ys,m) [] = (ys,m)
        loop (ys,m) ((c,l):zs) =
          if litPolarity l
            then loop (IM.insertWith (+) l c ys, m) zs
            else loop (IM.insertWith (+) (litNot l) (negate c) ys, m-c) zs

    -- 係数が0のものも取り除き、係数が負のリテラルを反転することで、
    -- 係数が正になるようにする。
    step2 :: ([(Integer,Lit)], Integer) -> ([(Integer,Lit)], Integer)
    step2 (xs,n) = loop ([],n) xs
      where
        loop (ys,m) [] = (ys,m)
        loop (ys,m) (t@(c,l):zs)
          | c == 0 = loop (ys,m) zs
          | c < 0  = loop ((negate c,litNot l):ys, m-c) zs
          | otherwise = loop (t:ys,m) zs

    -- degree以上の係数はそこで抑える。
    saturate :: Integer -> [(Integer,Lit)] -> [(Integer,Lit)]
    saturate n xs = [assert (c>0) (min n c, l) | (c,l) <- xs]

    -- omega test と同様の係数の gcd による単純化
    step3 :: ([(Integer,Lit)], Integer) -> ([(Integer,Lit)], Integer)
    step3 ([],n) = ([],n)
    step3 (xs,n) = ([(c `div` d, l) | (c,l) <- xs], (n+d-1) `div` d)
      where
        d = foldl1' gcd [c | (c,_) <- xs]

{-
-4*(not x1) + 3*x1 + 10*(not x2) >= 3
⇔ -4*(1 - x1) + 3*x1 + 10*(not x2) >= 3
⇔ -4 + 4*x1 + 3*x1 + 10*(not x2)>= 3
⇔ 7*x1 + 10*(not x2) >= 7
⇔ 7*x1 + 7*(not x2) >= 7
⇔ x1 + (not x2) >= 1
-}
test_normalizePBAtLeast :: ([(Integer, Lit)],Integer)
test_normalizePBAtLeast = normalizePBAtLeast ([(-4,-1),(3,1),(10,-2)], 3)

cutResolve :: ([(Integer,Lit)],Integer) -> ([(Integer,Lit)],Integer) -> Var -> ([(Integer,Lit)],Integer)
cutResolve (lhs1,rhs1) (lhs2,rhs2) v = assert (l1 == litNot l2) $ normalizePBAtLeast pb
  where
    (c1,l1) = head [(c,l) | (c,l) <- lhs1, litVar l == v]
    (c2,l2) = head [(c,l) | (c,l) <- lhs2, litVar l == v]
    g = gcd c1 c2
    s1 = c2 `div` g
    s2 = c1 `div` g
    pb = ([(s1*c,l) | (c,l) <- lhs1] ++ [(s2*c,l) | (c,l) <- lhs2], s1*rhs1 + s2 * rhs2)

test_cutResolve1 :: Bool
test_cutResolve1 = (sort lhs, rhs) == (sort [(1,3),(1,4)], 1)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    x4 = 4
    pb1 = ([(1,x1), (1,x2), (1,x3)], 1)
    pb2 = ([(2,-x1), (2,-x2), (1,x4)], 3)
    (lhs,rhs) = cutResolve pb1 pb2 x1

test_cutResolve2 :: Bool
test_cutResolve2 = (sort lhs, rhs) == (sort [(3,1),(2,-2),(2,4)], 3)
  where
    x1 = 1
    x2 = 2
    x3 = 3
    x4 = 4
    pb1 = ([(3,x1), (2,-x2), (1,x3), (1,x4)], 3)
    pb2 = ([(1,-x3), (1,x4)], 1)
    (lhs,rhs) = cutResolve pb1 pb2 x3

{--------------------------------------------------------------------
  internal data structures
--------------------------------------------------------------------}

type Level = Int
type LevelMap = IM.IntMap

levelRoot :: Level
levelRoot = -1

data Assignment
  = Assignment
  { aValue  :: !Bool
  , aLevel  :: {-# UNPACK #-} !Level
  , aReason :: !(Maybe SomeConstraint)
  , aBacktrackCBs :: !(IORef [IO ()])
  }

data VarData
  = VarData
  { vdAssignment :: !(IORef (Maybe Assignment))
  , vdPolarity   :: !(IORef Bool)
  , vdPosLitData :: !LitData
  , vdNegLitData :: !LitData
  , vdActivity   :: !(IORef VarActivity)
  }

newtype LitData
  = LitData
  { -- | will be invoked when this literal is falsified
    ldWatches :: IORef [SomeConstraint]
  }

newVarData :: IO VarData
newVarData = do
  ainfo <- newIORef Nothing
  polarity <- newIORef True
  pos <- newLitData
  neg <- newLitData
  activity <- newIORef 0
  return $ VarData ainfo polarity pos neg activity

newLitData :: IO LitData
newLitData = do
  ws <- newIORef []
  return $ LitData ws

varData :: Solver -> Var -> IO VarData
varData s !v = do
  a <- readIORef (svVarData s)
  unsafeRead a (v-1)

litData :: Solver -> Lit -> IO LitData
litData s !l =
  -- litVar による heap allocation を避けるために、
  -- litPolarityによる分岐後にvarDataを呼ぶ。
  if litPolarity l
    then do
      vd <- varData s l
      return $ vdPosLitData vd
    else do
      vd <- varData s (negate l)
      return $ vdNegLitData vd

{-# INLINE varValue #-}
varValue :: Solver -> Var -> IO LBool
varValue s !v = do
  vd <- varData s v
  m <- readIORef (vdAssignment vd)
  case m of
    Nothing -> return lUndef
    Just x -> return $! (liftBool $! aValue x)

{-# INLINE litValue #-}
litValue :: Solver -> Lit -> IO LBool
litValue s !l = do
  -- litVar による heap allocation を避けるために、
  -- litPolarityによる分岐後にvarDataを呼ぶ。
  if litPolarity l
    then varValue s l
    else do
      m <- varValue s (negate l)
      return $! lnot m

varLevel :: Solver -> Var -> IO Level
varLevel s !v = do
  vd <- varData s v
  m <- readIORef (vdAssignment vd)
  case m of
    Nothing -> error ("varLevel: unassigned var " ++ show v)
    Just a -> return (aLevel a)

litLevel :: Solver -> Lit -> IO Level
litLevel s l = varLevel s (litVar l)

varReason :: Solver -> Var -> IO (Maybe SomeConstraint)
varReason s !v = do
  vd <- varData s v
  m <- readIORef (vdAssignment vd)
  case m of
    Nothing -> error ("varReason: unassigned var " ++ show v)
    Just a -> return (aReason a)

-- | Solver instance
data Solver
  = Solver
  { svOk           :: !(IORef Bool)
  , svVarQueue     :: !(PQ.PriorityQueue (Var,VarActivity))
  , svAssigned     :: !(IORef (LevelMap [Lit]))
  , svVarCounter   :: !(IORef Int)
  , svVarData      :: !(IORef (IOArray Int VarData))
  , svClauseDB     :: !(IORef [SomeConstraint])
  , svLearntDB     :: !(IORef (Int,[SomeConstraint]))
  , svAssumptions  :: !(IORef (IOUArray Int Lit))
  , svLevel        :: !(IORef Level)
  , svBCPQueue     :: !(IORef (Seq.Seq Lit))
  , svModel        :: !(IORef (Maybe (VarMap Bool)))
  , svNDecision    :: !(IORef Int)
  , svNConflict    :: !(IORef Int)
  , svNRestart     :: !(IORef Int)

  -- | Inverse of the variable activity decay factor. (default 1 / 0.95)
  , svVarDecay     :: !(IORef Double)

  -- | Amount to bump next variable with.
  , svVarInc       :: !(IORef Double)

  -- | Inverse of the clause activity decay factor. (1 / 0.999)
  , svClaDecay     :: !(IORef Double)

  -- | Amount to bump next clause with.
  , svClaInc       :: !(IORef Double)

  -- | The initial restart limit. (default 100)
  , svRestartFirst :: !(IORef Int)

  -- | The factor with which the restart limit is multiplied in each restart. (default 1.5)
  , svRestartInc :: !(IORef Double)

  -- | The limit for learnt clauses is multiplied with this factor each restart. (default 1.1)
  , svLearntSizeInc :: !(IORef Double)

  -- | Controls conflict clause minimization (0=none, 1=local, 2=recursive)
  , svCCMin :: !(IORef Int)

  , svLogger :: !(IORef (Maybe (String -> IO ())))
  }

markBad :: Solver -> IO ()
markBad solver = writeIORef (svOk solver) False

bcpEnqueue :: Solver -> Lit -> IO ()
bcpEnqueue solver l = modifyIORef (svBCPQueue solver) (Seq.|> l)

bcpDequeue :: Solver -> IO (Maybe Lit)
bcpDequeue solver = do
  let ref = svBCPQueue solver
  ls <- readIORef ref
  case Seq.viewl ls of
    Seq.EmptyL -> return Nothing
    l Seq.:< ls' -> do
      writeIORef ref ls'
      return (Just l)

assignBy :: Constraint c => Solver -> Lit -> c -> IO Bool
assignBy solver lit c = assign_ solver lit (Just (toConstraint c))

assign :: Solver -> Lit -> IO Bool
assign solver lit = assign_ solver lit Nothing

assign_ :: Solver -> Lit -> Maybe SomeConstraint -> IO Bool
assign_ solver !lit reason = assert (validLit lit) $ do
  vd <- varData solver (litVar lit)
  m <- readIORef (vdAssignment vd)
  case m of
    Just a -> return $ litPolarity lit == aValue a
    Nothing -> do
      lv <- readIORef (svLevel solver)
      bt <- newIORef []

      writeIORef (vdAssignment vd) $ Just $
        Assignment
        { aValue  = litPolarity lit
        , aLevel  = lv
        , aReason = reason
        , aBacktrackCBs = bt
        }

      modifyIORef (svAssigned solver) (IM.insertWith (++) lv [lit])
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
    Nothing -> error "should not happen"
    Just a -> do
      writeIORef (vdPolarity vd) (aValue a)
      readIORef (aBacktrackCBs a) >>= sequence_
  writeIORef (vdAssignment vd) Nothing
  activity <- varActivity solver v
  PQ.enqueue (svVarQueue solver) (v,activity)

addBacktrackCB :: Solver -> Var -> IO () -> IO ()
addBacktrackCB solver !v callback = do
  vd <- varData solver v
  m <- readIORef (vdAssignment vd)
  case m of
    Nothing -> error "should not happen"
    Just a -> modifyIORef (aBacktrackCBs a) (callback :)

-- | Register the constraint to be notified when the literal becames false.
watch :: Constraint c => Solver -> Lit -> c -> IO ()
watch solver !lit c = do
  when debugMode $ do
    lits <- watchedLiterals solver c
    unless (lit `elem` lits) $ error "watch: should not happen"
  ld <- litData solver lit
  modifyIORef (ldWatches ld) (toConstraint c : )

-- | Returns list of constraints that are watching the literal.
watches :: Solver -> Lit -> IO [SomeConstraint]
watches solver !lit = do
  ld <- litData solver lit
  readIORef (ldWatches ld)

addToDB :: Constraint c => Solver -> c -> IO ()
addToDB solver c = do
  modifyIORef (svClauseDB solver) (toConstraint c : )
  when debugMode $ logIO solver $ do
    str <- showConstraint solver c
    return $ printf "constraint %s is added" str
  sanityCheck solver

addToLearntDB :: Constraint c => Solver -> c -> IO ()
addToLearntDB solver c = do
  modifyIORef (svLearntDB solver) $ \(n,xs) -> (n+1, toConstraint c : xs)
  when debugMode $ logIO solver $ do
    str <- showConstraint solver c
    return $ printf "constraint %s is added" str
  sanityCheck solver

reduceDB :: Solver -> IO ()
reduceDB solver = do
  (n,cs) <- readIORef (svLearntDB solver)

  xs <- forM cs $ \c@(ConstrClause (ClauseData a act)) -> do
    size <- liftM rangeSize (getBounds a)
    actval <- readIORef act
    return (c, (size <= 2, actval))

  -- Note that False <= True
  let ys = sortBy (compare `on` snd) xs
      (zs,ws) = splitAt (length ys `div` 2) ys

  let loop [] ret = return ret
      loop ((c,(isShort,_)) : rest) ret = do
        flag <- if isShort
                then return True
                else isLocked solver c
        if flag
          then loop rest (c:ret)
          else do
            detach solver c
            loop rest ret
  zs2 <- loop zs []

  let cs2 = zs2 ++ map fst ws
      n2 = length cs2

  when debugMode $ log solver $ printf "reduceDB: %d -> %d" n n2
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
  updateVarQueue solver

updateVarQueue :: Solver -> IO ()
updateVarQueue solver = do
  let vqueue = svVarQueue solver
  xs <- PQ.dequeueBatch vqueue
  forM_ xs $ \(v,_) -> do
    activity <- varActivity solver v
    PQ.enqueue vqueue (v,activity)

variables :: Solver -> IO [Var]
variables solver = do
  n <- nVars solver
  return [1 .. n]

-- | number of variables of the problem.
nVars :: Solver -> IO Int
nVars solver = do
  vcnt <- readIORef (svVarCounter solver)
  return $! (vcnt-1)

-- | number of assigned variables.
nAssigns :: Solver -> IO Int
nAssigns solver = do
  m <- readIORef (svAssigned solver)
  let f !r xs = r + length xs
  return $! IM.foldl' f 0 m

-- | number of clauses.
nClauses :: Solver -> IO Int
nClauses solver = do
  xs <- readIORef (svClauseDB solver)
  return $ length xs

-- | number of learnt constrints.
nLearnt :: Solver -> IO Int
nLearnt solver = do
  (n,_) <- readIORef (svLearntDB solver)
  return n

learnt :: Solver -> IO [SomeConstraint]
learnt solver = do
  (_,cs) <- readIORef (svLearntDB solver)
  return cs

{--------------------------------------------------------------------
  Solver
--------------------------------------------------------------------}

-- | Create a new Solver instance.
newSolver :: IO Solver
newSolver = do
  ok   <- newIORef True
  vcnt <- newIORef 1
  vqueue <- PQ.newPriorityQueueBy ltVar
  assigned <- newIORef IM.empty
  vars <- newIORef =<< newArray_ (1,0)
  db  <- newIORef []
  db2 <- newIORef (0,[])
  as  <- newIORef =<< newArray_ (0,-1)
  lv  <- newIORef levelRoot
  q   <- newIORef Seq.empty
  m   <- newIORef Nothing
  ndecision <- newIORef 0
  nconflict <- newIORef 0
  nrestart  <- newIORef 0

  claDecay <- newIORef (1 / 0.999)
  claInc   <- newIORef 1
  varDecay <- newIORef (1 / 0.95)
  varInc   <- newIORef 1
  restartFirst <- newIORef defaultRestartFirst
  restartInc <- newIORef defaultRestartInc
  learntSizeInc <- newIORef defaultLearntSizeInc
  ccMin <- newIORef defaultCCMin

  logger <- newIORef Nothing

  return $
    Solver
    { svOk = ok
    , svVarCounter = vcnt
    , svVarQueue   = vqueue
    , svAssigned   = assigned
    , svVarData    = vars
    , svClauseDB   = db
    , svLearntDB   = db2
    , svAssumptions = as
    , svLevel      = lv
    , svBCPQueue   = q
    , svModel      = m
    , svNDecision  = ndecision
    , svNConflict  = nconflict
    , svNRestart   = nrestart
    , svVarDecay   = varDecay
    , svVarInc     = varInc
    , svClaDecay   = claDecay
    , svClaInc     = claInc
    , svRestartFirst = restartFirst
    , svRestartInc   = restartInc
    , svLearntSizeInc = learntSizeInc
    , svCCMin = ccMin
    , svLogger = logger
    }

ltVar :: (Var,VarActivity) -> (Var,VarActivity) -> Bool
ltVar = (>) `on` snd

{--------------------------------------------------------------------
  Problem specification
--------------------------------------------------------------------}

-- |Add a new variable
newVar :: Solver -> IO Var
newVar s = do
  v <- readIORef (svVarCounter s)
  writeIORef (svVarCounter s) (v+1)
  PQ.enqueue (svVarQueue s) (v,0)
  vd <- newVarData

  a <- readIORef (svVarData s)
  (_,ub) <- getBounds a
  if v <= ub
    then writeArray a v vd
    else do
      let ub' = max 2 (ub * 3 `div` 2)
      a' <- newArray_ (1,ub')
      forM_ [1..ub] $ \v2 -> do
        vd2 <- readArray a v2
        writeArray a' v2 vd2
      writeArray a' v vd
      writeIORef (svVarData s) a'

  return v

-- |Add a clause to the solver.
addClause :: Solver -> Clause -> IO ()
addClause solver lits = do
  d <- readIORef (svLevel solver)
  assert (d == levelRoot) $ return ()

  lits2 <- instantiateClause solver lits
  case normalizeClause =<< lits2 of
    Nothing -> return ()
    Just [] -> markBad solver
    Just [lit] -> do
      ret <- assign solver lit
      assert ret $ return ()
      ret2 <- deduce solver
      case ret2 of
        Nothing -> return ()
        Just _ -> markBad solver
    Just lits3 -> do
      clause <- newClauseData lits3 False
      attach solver clause
      addToDB solver clause

-- | Add a cardinality constraints /atleast({l1,l2,..},n)/.
addAtLeast :: Solver -- ^ The 'Solver' argument.
           -> [Lit]  -- ^ set of literals /{l1,l2,..}/ (duplicated elements are ignored)
           -> Int    -- ^ /n/.
           -> IO ()
addAtLeast solver lits n = do
  d <- readIORef (svLevel solver)
  assert (d == levelRoot) $ return ()

  (lits',n') <- liftM normalizeAtLeast $ instantiateAtLeast solver (lits,n)
  let len = length lits'

  if n' <= 0 then return ()
    else if n' > len then markBad solver
    else if n' == 1 then addClause solver lits'
    else if n' == len then do
      forM_ lits' $ \l -> do
        ret <- assign solver l
        assert ret $ return ()
        ret2 <- deduce solver
        case ret2 of
          Nothing -> return ()
          Just _ -> markBad solver
    else do
      c <- newAtLeastData lits' n'
      attach solver c
      addToDB solver c

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
           -> [Lit]  -- ^ set of literals /{l1,l2,..}/ (duplicated elements are ignored)1
           -> Int    -- ^ /n/
           -> IO ()
addExactly solver lits n = do
  addAtLeast solver lits n
  addAtMost solver lits n

-- | Add a pseudo boolean constraints /c1*l1 + c2*l2 + … ≥ n/.
addPBAtLeast :: Solver          -- ^ The 'Solver' argument.
             -> [(Integer,Lit)] -- ^ set of terms @[(c1,l1),(c2,l2),…]@
             -> Integer         -- ^ /n/.
             -> IO ()
addPBAtLeast solver ts n = do
  d <- readIORef (svLevel solver)
  assert (d == levelRoot) $ return ()

  (ts',degree) <- liftM normalizePBAtLeast $ instantiatePBAtLeast solver (ts,n)
  let cs = map fst ts'
      slack = sum cs - degree

  if degree <= 0 then return ()
    else if slack < 0 then markBad solver
    else if Set.size (Set.fromList cs) == 1 then do
      let c = head cs
      addAtLeast solver (map snd ts') (fromInteger ((degree+c-1) `div` c))
    else do
      forM_ ts' $ \(c,l) -> do
        when (slack - c < 0) $ do
          ret <- assign solver l
          assert ret $ return ()
      ret <- deduce solver
      case ret of
        Nothing -> return ()
        Just _ -> markBad solver

      ok <- readIORef (svOk solver)
      when ok $ do
        c <- newPBAtLeastData ts' degree
        attach solver c
        addToDB solver c

-- | Add a pseudo boolean constraints /c1*l1 + c2*l2 + … ≤ n/.
addPBAtMost :: Solver          -- ^ The 'Solver' argument.
            -> [(Integer,Lit)] -- ^ list of @[(c1,l1),(c2,l2),…]@
            -> Integer         -- ^ /n/.
            -> IO ()
addPBAtMost solver ts n = addPBAtLeast solver [(-c,l) | (c,l) <- ts] (negate n)

-- | Add a pseudo boolean constraints /c1*l1 + c2*l2 + … = n/.
addPBExactly :: Solver          -- ^ The 'Solver' argument.
             -> [(Integer,Lit)] -- ^ list of terms @[(c1,l1),(c2,l2),…]@
             -> Integer         -- ^ /n/.
             -> IO ()
addPBExactly solver ts n = do
  addPBAtLeast solver ts n
  addPBAtMost solver ts n

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
  writeIORef (svModel solver) Nothing

  ok <- readIORef (svOk solver)
  if not ok
    then return False
    else do
      when debugMode $ dumpVarActivity solver
      updateVarQueue solver
      d <- readIORef (svLevel solver)
      assert (d == levelRoot) $ return ()

      restartFirst  <- readIORef (svRestartFirst solver)
      restartInc    <- readIORef (svRestartInc solver)
      learntSizeInc <- readIORef (svLearntSizeInc solver)

      let loop !conflict_lim learnt_lim = do
            ret <- search solver conflict_lim learnt_lim
            case ret of
              Just x -> return x
              Nothing -> do
                modifyIORef' (svNRestart solver) (+1)
                backtrackTo solver levelRoot
                loop (ceiling (fromIntegral conflict_lim * restartInc))
                     (ceiling (fromIntegral learnt_lim * learntSizeInc))

      nc <- nClauses solver
      nv <- nVars solver
      let learntSizeFirst = max (nc + 2*nv) 16

      start <- getCPUTime
      result <- loop restartFirst learntSizeFirst
      end <- getCPUTime

      when result $ do
        when debugMode $ checkSatisfied solver
        constructModel solver

      backtrackTo solver levelRoot

      when debugMode $ dumpVarActivity solver
      when debugMode $ dumpClaActivity solver
      (log solver . printf "solving time = %.3fs") (fromIntegral (end - start) / 10^(12::Int) :: Double)
      (log solver . printf "#decision = %d") =<< readIORef (svNDecision solver)
      (log solver . printf "#conflict = %d") =<< readIORef (svNConflict solver)
      (log solver . printf "#restart = %d")  =<< readIORef (svNRestart solver)

      return result

search :: Solver -> Int -> Int -> IO (Maybe Bool)
search solver !conflict_lim !learnt_lim = loop 0
  where
    loop :: Int -> IO (Maybe Bool)
    loop !c = do
      sanityCheck solver
      conflict <- deduce solver
      sanityCheck solver

      case conflict of
        Nothing -> do
          n <- nLearnt solver
          when (learnt_lim >= 0 && n > learnt_lim) $ reduceDB solver

          r <- pickAssumption
          case r of
            Nothing -> return (Just False)
            Just lit
              | lit /= litUndef -> decide solver lit >> loop c
              | otherwise -> do
                  lit2 <- pickBranchLit solver
                  if lit2 == litUndef
                    then return (Just True)
                    else decide solver lit2 >> loop c

        Just constr -> do
          varDecayActivity solver
          constrDecayActivity solver

          modifyIORef' (svNConflict solver) (+1)
          d <- readIORef (svLevel solver)

          when debugMode $ logIO solver $ do
            str <- showConstraint solver constr
            return $ printf "conflict(level=%d): %s" d str

          if d == levelRoot
            then return (Just False)
            else if conflict_lim >= 0 && c+1 >= conflict_lim then
              return Nothing
            else do
              (learntClause, level) <- analyzeConflict solver constr
              backtrackTo solver level
              case learntClause of
                [] -> error "should not happen"
                [lit] -> do
                  ret <- assign solver lit
                  assert ret $ return ()
                  return ()
                lit:_ -> do
                  cl <- newClauseData learntClause True
                  attach solver cl
                  addToLearntDB solver cl
                  assignBy solver lit cl
                  constrBumpActivity solver cl
              loop (c+1)

    pickAssumption :: IO (Maybe Lit)
    pickAssumption = do
      !as <- readIORef (svAssumptions solver)
      !b <- getBounds as
      let go = do
              d <- readIORef (svLevel solver)
              if not (inRange b (d+1))
                then return (Just litUndef)
                else do
                  l <- readArray as (d+1)
                  val <- litValue solver l
                  if val == lTrue then do
                     -- dummy decision level
                     modifyIORef' (svLevel solver) (+1)
                     go
                   else if val == lFalse then
                     -- conflict with assumption
                     return Nothing
                   else
                     return (Just l)
      go


-- | A model is represented as a mapping from variables to its values.
type Model = IM.IntMap Bool

-- | After 'solve' returns True, it returns the model.
model :: Solver -> IO Model
model solver = do
  m <- readIORef (svModel solver)
  return (fromJust m)

{--------------------------------------------------------------------
  Parameter settings.
--------------------------------------------------------------------}

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

{--------------------------------------------------------------------
  API for implementation of @solve@
--------------------------------------------------------------------}

pickBranchLit :: Solver -> IO Lit
pickBranchLit !solver = do
  let vqueue = svVarQueue solver

      loop :: IO Lit
      loop = do
        m <- PQ.dequeue vqueue
        case m of
          Nothing -> return litUndef
          Just (var,_) -> do
            val <- varValue solver var
            if val /= lUndef
              then loop
              else do
                vd <- varData solver var
                p <- readIORef (vdPolarity vd)
                let lit = literal var p
                seq lit $ return lit
  loop

decide :: Solver -> Lit -> IO ()
decide solver !lit = do
  modifyIORef' (svNDecision solver) (+1)
  modifyIORef' (svLevel solver) (+1)
  when debugMode $ do
    val <- litValue solver lit
    when (val /= lUndef) $ error "decide: should not happen"
  assign solver lit
  return ()

deduce :: Solver -> IO (Maybe SomeConstraint)
deduce solver = loop
  where
    loop :: IO (Maybe SomeConstraint)
    loop = do
      r <- bcpDequeue solver
      case r of
        Nothing -> return Nothing
        Just lit -> do
          ret <- processLit lit
          case ret of
            Just _ -> return ret
            Nothing -> loop

    processLit :: Lit -> IO (Maybe SomeConstraint)
    processLit !lit = do
      let lit2 = litNot lit
      ld <- litData solver lit2
      let wsref = ldWatches ld
      let loop2 [] = return Nothing
          loop2 (w:ws) = do
            ok <- propagate solver w lit2
            if ok
              then loop2 ws
              else do
                modifyIORef wsref (++ws)
                return (Just w)
      ws <- readIORef wsref
      writeIORef wsref []
      loop2 ws

analyzeConflict :: Constraint c => Solver -> c -> IO (Clause, Level)
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

  let pop :: IO (Maybe Lit)
      pop = do
        m <- readIORef (svAssigned solver)
        case IM.lookup d m of
          Just (l:ls) -> do
            writeIORef (svAssigned solver) (IM.insert d ls m)
            return $ Just l
          _ -> return Nothing

  let loop :: LitSet -> LitSet -> IO LitSet
      loop lits1 lits2
        | sz==1 = do
            return $ lits1 `IS.union` lits2
        | sz>=2 = do
            ret <- pop
            case ret of
              Nothing -> do
                error $ printf "analyzeConflict: should not happen: empty trail: loop %s %s"
                               (show lits1) (show lits2)
              Just l -> do
                if litNot l `IS.notMember` lits1
                 then do
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

  lits <- do
    ccmin <- readIORef (svCCMin solver)
    if ccmin >= 2 then
       minimizeConflictClauseRecursive solver lits
     else if ccmin >= 1 then
       minimizeConflictClauseLocal solver lits
     else
       return lits

  when debugMode $ do
    let f l = do
          lv <- litLevel solver l
          return $ lv >= d
    litsd <- filterM f (IS.toList lits)
    when (length litsd /= 1) $ do
      xs <- forM (IS.toList lits) $ \l -> do
        lv <- litLevel solver l
        return (l,lv)
      error $ printf "analyzeConflict: not assertive: %s" (show xs)

  xs <- liftM (sortBy (flip (compare `on` snd))) $
    forM (IS.toList lits) $ \l -> do
      lv <- litLevel solver l
      return (l,lv)

  let level = case xs of
                [] -> error "analyzeConflict: should not happen"
                [_] -> levelRoot
                _:(_,lv):_ -> lv
  return (map fst xs, level)

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
      if lv == levelRoot || lit `IS.member` lits || lit `IS.member` seen
        then go ls seen
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

-- | Revert to the state at given level
-- (keeping all assignment at @level@ but not beyond).
backtrackTo :: Solver -> Int -> IO ()
backtrackTo solver level = do
  when debugMode $ log solver $ printf "backtrackTo: %d" level
  m <- readIORef (svAssigned solver)
  m' <- loop m
  writeIORef (svAssigned solver) m'
  writeIORef (svBCPQueue solver) Seq.empty
  writeIORef (svLevel solver) level
  where
    loop :: LevelMap [Lit] -> IO (LevelMap [Lit])
    loop m =
      case IM.maxViewWithKey m of
        Just ((lv,lits),m') | level < lv -> do
          forM_ lits $ \lit -> unassign solver (litVar lit)
          loop m'
        _ -> return m

constructModel :: Solver -> IO ()
constructModel solver = do
  vs <- variables solver
  xs <- forM vs $ \v -> do
    vd <- varData solver v
    a <- readIORef (vdAssignment vd)
    return $ (v, aValue (fromJust a))
  let m = IM.fromAscList xs
  writeIORef (svModel solver) (Just m)

constrDecayActivity :: Solver -> IO ()
constrDecayActivity solver = do
  d <- readIORef (svClaDecay solver)
  modifyIORef' (svClaInc solver) (d*)

constrRescaleAllActivity :: Solver -> IO ()
constrRescaleAllActivity solver = do
  xs <- learnt solver
  forM_ xs $ \c -> constrRescaleActivity solver c
  modifyIORef' (svClaInc solver) (* 1e-20)

{--------------------------------------------------------------------
  constraint implementation
--------------------------------------------------------------------}

class Constraint a where
  toConstraint :: a -> SomeConstraint

  showConstraint :: Solver -> a -> IO String

  attach :: Solver -> a -> IO ()

  watchedLiterals :: Solver -> a -> IO [Lit]

  -- | invoked with the watched literal when the literal is falsified.
  -- 'watch' で 'toConstraint' を呼び出して heap allocation が発生するのを
  -- 避けるために、元の 'SomeConstraint' も渡しておく。
  basicPropagate :: Solver -> SomeConstraint -> a -> Lit -> IO Bool

  -- | deduce a clause C∨l from the constraint and return C.
  -- C and l should be false and true respectively under the current
  -- assignment.
  basicReasonOf :: Solver -> a -> Maybe Lit -> IO Clause

  isSatisfied :: Solver -> a -> IO Bool

  constrBumpActivity :: Solver -> a -> IO ()
  constrBumpActivity _ _ = return ()

  constrRescaleActivity :: Solver -> a -> IO ()
  constrRescaleActivity _ _ = return ()

detach :: Constraint a => Solver -> a -> IO ()
detach solver c = do
  let c2 = toConstraint c
  lits <- watchedLiterals solver c
  forM_ lits $ \lit -> do
    ld <- litData solver lit
    modifyIORef' (ldWatches ld) (delete c2)

-- | invoked with the watched literal when the literal is falsified.
propagate :: Solver -> SomeConstraint -> Lit -> IO Bool
propagate solver c l = basicPropagate solver c c l

-- | deduce a clause C∨l from the constraint and return C.
-- C and l should be false and true respectively under the current
-- assignment.
reasonOf :: Constraint a => Solver -> a -> Maybe Lit -> IO Clause
reasonOf solver c x = do
  when debugMode $
    case x of
      Nothing -> return ()
      Just lit -> do
        val <- litValue solver lit
        unless (lTrue == val) $ do
          str <- showConstraint solver c
          error (printf "reasonOf: value of literal %d should be True but %s (basicReasonOf %s %s)" lit (show val) str (show x))
  cl <- basicReasonOf solver c x
  when debugMode $ do
    forM_ cl $ \lit -> do
      val <- litValue solver lit
      unless (lFalse == val) $ do
        str <- showConstraint solver c
        error (printf "reasonOf: value of literal %d should be False but %s (basicReasonOf %s %s)" lit (show val) str (show x))
  return cl

isLocked :: Solver -> SomeConstraint -> IO Bool
isLocked solver c = anyM p =<< watchedLiterals solver c
  where
    p :: Lit -> IO Bool
    p lit = do
      val <- litValue solver lit
      if val /= lTrue
        then return False
        else do
          m <- varReason solver (litVar lit)
          case m of
            Nothing -> return False
            Just c2 -> return $! c == c2

data SomeConstraint
  = ConstrClause !ClauseData
  | ConstrAtLeast !AtLeastData
  | ConstrPBAtLeast !PBAtLeastData
  deriving Eq

instance Constraint SomeConstraint where
  toConstraint = id

  showConstraint s (ConstrClause c)    = showConstraint s c
  showConstraint s (ConstrAtLeast c)   = showConstraint s c
  showConstraint s (ConstrPBAtLeast c) = showConstraint s c

  attach s (ConstrClause c)    = attach s c
  attach s (ConstrAtLeast c)   = attach s c
  attach s (ConstrPBAtLeast c) = attach s c

  watchedLiterals s (ConstrClause c)    = watchedLiterals s c
  watchedLiterals s (ConstrAtLeast c)   = watchedLiterals s c
  watchedLiterals s (ConstrPBAtLeast c) = watchedLiterals s c

  basicPropagate s this (ConstrClause c)  lit   = basicPropagate s this c lit
  basicPropagate s this (ConstrAtLeast c) lit   = basicPropagate s this c lit
  basicPropagate s this (ConstrPBAtLeast c) lit = basicPropagate s this c lit

  basicReasonOf s (ConstrClause c)  l   = basicReasonOf s c l
  basicReasonOf s (ConstrAtLeast c) l   = basicReasonOf s c l
  basicReasonOf s (ConstrPBAtLeast c) l = basicReasonOf s c l

  isSatisfied s (ConstrClause c)    = isSatisfied s c
  isSatisfied s (ConstrAtLeast c)   = isSatisfied s c
  isSatisfied s (ConstrPBAtLeast c) = isSatisfied s c

  constrBumpActivity s (ConstrClause c)    = constrBumpActivity s c
  constrBumpActivity s (ConstrAtLeast c)   = constrBumpActivity s c
  constrBumpActivity s (ConstrPBAtLeast c) = constrBumpActivity s c

  constrRescaleActivity s (ConstrClause c)    = constrRescaleActivity s c
  constrRescaleActivity s (ConstrAtLeast c)   = constrRescaleActivity s c
  constrRescaleActivity s (ConstrPBAtLeast c) = constrRescaleActivity s c

{--------------------------------------------------------------------
  Clause
--------------------------------------------------------------------}

data ClauseData
  = ClauseData
  { claLits :: !(IOUArray Int Lit)
  , claActivity :: !(IORef Double)
  }

instance Eq ClauseData where
  c1 == c2 = claActivity c1 == claActivity c2

newClauseData :: Clause -> Bool -> IO ClauseData
newClauseData ls learnt = do
  let size = length ls
  a <- newListArray (0, size-1) ls
  act <- newIORef $! (if learnt then 0 else -1)
  return (ClauseData a act)

instance Constraint ClauseData where
  toConstraint = ConstrClause

  showConstraint _ this = do
    lits <- getElems (claLits this)
    return (show lits)

  attach solver this = do
    lits <- getElems (claLits this)
    case lits of
      l1:l2:_ -> do
        watch solver l1 this
        watch solver l2 this
      _ -> return ()

  watchedLiterals _ this = do
    lits <- getElems (claLits this)
    case lits of
      l1:l2:_ -> return [l1, l2]
      _ -> return []

  basicPropagate !s this this2 !falsifiedLit = do
    preprocess

    !lit0 <- unsafeRead a 0
    !val0 <- litValue s lit0
    if val0 == lTrue
      then do
        watch s falsifiedLit this
        return True
      else do
        (!lb,!ub) <- getBounds a
        assert (lb==0) $ return ()
        i <- findForWatch 2 ub
        case i of
          -1 -> do
            when debugMode $ logIO s $ do
               str <- showConstraint s this
               return $ printf "basicPropagate: %s is unit" str
            watch s falsifiedLit this
            assignBy s lit0 this
          _  -> do
            !lit1 <- unsafeRead a 1
            !liti <- unsafeRead a i
            unsafeWrite a 1 liti
            unsafeWrite a i lit1
            watch s liti this
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

      -- Maybe を heap allocation するのを避けるために、
      -- 見つからなかったときは -1 を返すことに。
      findForWatch :: Int -> Int -> IO Int
      findForWatch i end | i > end = return (-1)
      findForWatch i end = do
        val <- litValue s =<< unsafeRead a i
        if val /= lFalse
          then return i
          else findForWatch (i+1) end

  basicReasonOf _ this l = do
    lits <- getElems (claLits this)
    case l of
      Nothing -> return lits
      Just lit -> do
        assert (lit == head lits) $ return ()
        return $ tail lits

  isSatisfied solver this = do
    lits <- getElems (claLits this)
    vals <- mapM (litValue solver) lits
    return $ lTrue `elem` vals

  constrBumpActivity solver this = do
    let act = claActivity this
    aval <- readIORef act
    when (aval >= 0) $ do -- learnt clause
      inc <- readIORef (svClaInc solver)
      let aval2 = aval+inc
      writeIORef act $! aval2
      when (aval2 > 1e20) $
        -- Rescale
        constrRescaleAllActivity solver

  constrRescaleActivity _ this = do
    let act = claActivity this
    aval <- readIORef act
    when (aval >= 0) $ writeIORef act $! (aval * 1e-20)

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

{--------------------------------------------------------------------
  Cardinality Constraint
--------------------------------------------------------------------}

data AtLeastData
  = AtLeastData
  { atLeastLits :: IOUArray Int Lit
  , atLeastNum :: !Int
  , atLeastActivity :: !(IORef Double)
  }
  deriving Eq

newAtLeastData :: [Lit] -> Int -> IO AtLeastData
newAtLeastData ls n = do
  let size = length ls
  a <- newListArray (0, size-1) ls
  let learnt = False -- FIXME
  act <- newIORef $! (if learnt then 0 else -1)
  return (AtLeastData a n act)

instance Constraint AtLeastData where
  toConstraint = ConstrAtLeast

  showConstraint _ this = do
    lits <- getElems (atLeastLits this)
    return $ show lits ++ " >= " ++ show (atLeastNum this)

  attach solver this = do
    lits <- getElems (atLeastLits this)
    let n = atLeastNum this
    let ws = if length lits > n then take (n+1) lits else []
    forM_ ws $ \l -> watch solver l this

  watchedLiterals _ this = do
    lits <- getElems (atLeastLits this)
    let n = atLeastNum this
    let ws = if length lits > n then take (n+1) lits else []
    return ws

  basicPropagate s this this2 falsifiedLit = do
    preprocess

    when debugMode $ do
      litn <- readArray a n
      unless (litn == falsifiedLit) $ error "AtLeastData.basicPropagate: should not happen"

    (lb,ub) <- getBounds a
    assert (lb==0) $ return ()
    ret <- findForWatch (n+1) ub
    case ret of
      Nothing -> do
        when debugMode $ logIO s $ do
          str <- showConstraint s this
          return $ printf "basicPropagate: %s is unit" str
        watch s falsifiedLit this
        let loop :: Int -> IO Bool
            loop i
              | i >= n = return True
              | otherwise = do
                  liti <- readArray a i
                  ret2 <- assignBy s liti this
                  if ret2
                    then loop (i+1)
                    else return False
        loop 0
      Just i  -> do
        liti <- readArray a i
        litn <- readArray a n
        writeArray a i litn
        writeArray a n liti
        watch s liti this
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
              li <- readArray a i
              if (li /= falsifiedLit)
                then loop (i+1)
                else do
                  ln <- readArray a n
                  writeArray a n li
                  writeArray a i ln

      findForWatch :: Int -> Int -> IO (Maybe Int)
      findForWatch i end | i > end = return Nothing
      findForWatch i end = do
        val <- litValue s =<< readArray a i
        if val /= lFalse
          then return (Just i)
          else findForWatch (i+1) end

  basicReasonOf s this l = do
    lits <- getElems (atLeastLits this)
    let n = atLeastNum this
    case l of
      Nothing -> do
        let f :: [Lit] -> IO Lit
            f [] = error "AtLeastData.basicReasonOf: should not happen"
            f (l:ls) = do
              val <- litValue s l
              if val == lFalse
                then return l
                else f ls
        lit <- f (take n lits)
        return $ lit : drop n lits
      Just lit -> do
        assert (lit `elem` take n lits) $ return ()
        return $ drop n lits

  isSatisfied solver this = do
    lits <- getElems (atLeastLits this)
    vals <- mapM (litValue solver) lits
    return $ length [v | v <- vals, v == lTrue] >= atLeastNum this

  constrBumpActivity solver this = do
    let act = atLeastActivity this
    aval <- readIORef act
    when (aval >= 0) $ do -- learnt clause
      inc <- readIORef (svClaInc solver)
      let aval2 = aval+inc
      writeIORef act $! aval2
      when (aval2 > 1e20) $
        -- Rescale
        constrRescaleAllActivity solver

  constrRescaleActivity _ this = do
    let act = atLeastActivity this
    aval <- readIORef act
    when (aval >= 0) $ writeIORef act $! (aval * 1e-20)

instantiateAtLeast :: Solver -> ([Lit],Int) -> IO ([Lit],Int)
instantiateAtLeast solver (xs,n) = loop ([],n) xs
  where
    loop :: ([Lit],Int) -> [Lit] -> IO ([Lit],Int)
    loop ret [] = return ret
    loop (ys,n) (l:ls) = do
      val <- litValue solver l
      if val == lTrue then
         loop (ys, n-1) ls
       else if val == lFalse then
         loop (ys, n) ls
       else
         loop (l:ys, n) ls

{--------------------------------------------------------------------
  Pseudo Boolean Constraint
--------------------------------------------------------------------}

data PBAtLeastData
  = PBAtLeastData
  { pbTerms  :: !(LitMap Integer)
  , pbDegree :: !Integer
  , pbSlack  :: !(IORef Integer)
  , pbActivity :: !(IORef Double)
  }
  deriving Eq

newPBAtLeastData :: [(Integer,Lit)] -> Integer -> IO PBAtLeastData
newPBAtLeastData ts degree = do
  let slack = sum (map fst ts) - degree
      m = IM.fromList [(l,c) | (c,l) <- ts]
  s <- newIORef slack
  let learnt = False -- FIXME
  act <- newIORef $! (if learnt then 0 else -1)
  return (PBAtLeastData m degree s act)

instance Constraint PBAtLeastData where
  toConstraint = ConstrPBAtLeast

  showConstraint _ this = do
    return $ show [(c,l) | (l,c) <- IM.toList (pbTerms this)] ++ " >= " ++ show (pbDegree this)

  attach solver this = do
    forM_ (IM.keys (pbTerms this)) $ \l -> watch solver l this

  watchedLiterals _ this = do
    return $ IM.keys $ pbTerms this

  basicPropagate solver this this2 falsifiedLit = do
    watch solver falsifiedLit this

    let c = pbTerms this2 IM.! falsifiedLit
    let slack = pbSlack this2
    modifyIORef' slack (subtract c)
    addBacktrackCB solver (litVar falsifiedLit) $ modifyIORef' slack (+ c)
    s <- readIORef slack

    if s < 0
      then return False
      else do
        let ls = [l1 | (l1,c1) <- IM.toList (pbTerms this2), c1 > s]
        when (not (null ls)) $ do
          when debugMode $ logIO solver $ do
            str <- showConstraint solver this
            return $ printf "basicPropagate: %s is unit (new slack = %d)" str s
          forM_ ls $ \l1 -> do
            v <- litValue solver l1
            when (v == lUndef) $ do
              assignBy solver l1 this
              return ()
        return True

  basicReasonOf solver this l = do
    let m = pbTerms this
    xs <- do
      tmp <- filterM (\(lit,_) -> liftM (lFalse ==) (litValue solver lit)) (IM.toList m)
      return $ sortBy (flip compare `on` snd) tmp
    let max_slack = sum (map snd $ IM.toList m) - pbDegree this
    case l of
      Nothing -> return $ f max_slack xs
      Just lit -> return $ f (max_slack - (m IM.! lit)) xs
    where
      f :: Integer -> [(Lit,Integer)] -> [Lit]
      f s xs = go s xs []

      go :: Integer -> [(Lit,Integer)] -> [Lit] -> [Lit]
      go s _ ret | s < 0 = ret
      go _ [] _ = error "should not happen"
      go s ((lit,c):xs) ret = go (s - c) xs (lit:ret)

  isSatisfied solver this = do
    xs <- forM (IM.toList (pbTerms this)) $ \(l,c) -> do
      v <- litValue solver l
      if v == lTrue
        then return c
        else return 0
    return $ sum xs >= pbDegree this

  constrBumpActivity solver this = do
    let act = pbActivity this
    aval <- readIORef act
    when (aval >= 0) $ do -- learnt clause
      inc <- readIORef (svClaInc solver)
      let aval2 = aval+inc
      writeIORef act $! aval2
      when (aval2 > 1e20) $
        -- Rescale
        constrRescaleAllActivity solver

  constrRescaleActivity _ this = do
    let act = pbActivity this
    aval <- readIORef act
    when (aval >= 0) $ writeIORef act $! (aval * 1e-20)

instantiatePBAtLeast :: Solver -> ([(Integer,Lit)],Integer) -> IO ([(Integer,Lit)],Integer)
instantiatePBAtLeast solver (xs,n) = loop ([],n) xs
  where
    loop :: ([(Integer,Lit)],Integer) -> [(Integer,Lit)] -> IO ([(Integer,Lit)],Integer)
    loop ret [] = return ret
    loop (ys,n) ((c,l):ts) = do
      val <- litValue solver l
      if val == lTrue then
         loop (ys, n-c) ts
       else if val == lFalse then
         loop (ys, n) ts
       else
         loop ((c,l):ys, n) ts

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

modifyIORef' :: IORef a -> (a -> a) -> IO ()
modifyIORef' ref f = do
  x <- readIORef ref
  writeIORef ref $! f x

{--------------------------------------------------------------------
  debug
--------------------------------------------------------------------}

debugMode :: Bool
debugMode = False

checkSatisfied :: Solver -> IO ()
checkSatisfied solver = do
  cls <- readIORef (svClauseDB solver)
  xs <- mapM (isSatisfied solver) cls
  assert (and xs) $ return ()

sanityCheck :: Solver -> IO ()
sanityCheck _ | not debugMode = return ()
sanityCheck solver = do
  cls <- readIORef (svClauseDB solver)
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

dumpClaActivity :: Solver -> IO ()
dumpClaActivity solver = do
  log solver "Learnt clause activity:"
  xs <- learnt solver
  forM_ xs $ \c@(ConstrClause cla) -> do
    s <- showConstraint solver c
    aval <- readIORef (claActivity cla)
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
