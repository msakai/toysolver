{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
{-# LANGUAGE BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  SAT
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
--
-- A toy-level SAT solver based on CDCL.
--
-- TODO:
--
-- * XOR clause
--
-- * VSIDS heauristics
--
-- * Clause deletion
--
-- * RESTART
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

--  -- * Read state

  -- * Extract results
  , Model
  , model

  -- * Internal API
  , normalizePBAtLeast
  ) where

import Control.Monad
import Control.Exception
import Data.Array.IO
import Data.Function
import Data.IORef
import Data.List
import Data.Maybe
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Set as Set
import qualified Data.Sequence as Seq
import qualified Data.PriorityQueue as PQ
import qualified Data.Vector as V
import System.IO
import Text.Printf
import LBool

{--------------------------------------------------------------------
  pure/persistent data structures
--------------------------------------------------------------------}

-- | Variable is represented as positive integers (DIMACS format).
type Var = Int

type VarSet = IS.IntSet
type VarMap = IM.IntMap

validVar :: Var -> Bool
validVar v = v > 0

{-# INLINE varToIdx #-}
varToIdx :: Var -> Int
varToIdx v = v - 1

-- | Positive (resp. negative) literals are represented as positive (resp.
-- negative) integers. (DIMACS format).
type Lit = Int

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

normalizePBAtLeast :: ([(Integer,Lit)], Integer) -> ([(Integer,Lit)], Integer)
normalizePBAtLeast a =
　case step2 $ step1 $ a of
    (xs,n)
      | n > 0     -> (saturate n xs, n)
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

    -- TODO: 係数のgcdをとって割ったりとかもする?

{-
-4*(not x1) + 3*x1 + 10*(not x2) >= 3
⇔ -4*(1 - x1) + 3*x1 + 10*(not x2) >= 3
⇔ -4 + 4*x1 + 3*x1 + 10*(not x2)>= 3
⇔ 7*x1 + 10*(not x2) >= 7
⇒ 7*x1 + 7*(not x2) >= 7
-}
test_normalizePBAtLeast :: ([(Integer, Lit)],Integer)
test_normalizePBAtLeast = normalizePBAtLeast ([(-4,-1),(3,1),(10,-2)], 3)

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
  , vdScore      :: !(IORef VarScore)
  }

data LitData
  = LitData
  { -- | will be invoked when this literal is falsified
    ldWatches :: !(IORef [SomeConstraint])
  }

newVarData :: IO VarData
newVarData = do
  ainfo <- newIORef Nothing
  polarity <- newIORef True
  pos <- newLitData
  neg <- newLitData
  score <- newIORef 0
  return $ VarData ainfo polarity pos neg score

newLitData :: IO LitData
newLitData = do
  ws <- newIORef []
  return $ LitData ws

varData :: Solver -> Var -> IO VarData
varData s !v = do
  vec <- readIORef (svVarData s)
  let idx = varToIdx v
  seq idx (return $! vec V.! idx)

litData :: Solver -> Lit -> IO LitData
litData s l = do
  vd <- varData s (litVar l)
  return $!
    if litPolarity l
    then vdPosLitData vd
    else vdNegLitData vd

{-# INLINE varValue #-}
varValue :: Solver -> Var -> IO LBool
varValue s v = do
  vd <- varData s v
  m <- readIORef (vdAssignment vd)
  case m of
    Nothing -> return lUndef
    Just x -> return $! (liftBool $! aValue x)

{-# INLINE litValue #-}
litValue :: Solver -> Lit -> IO LBool
litValue s l = do
  m <- varValue s (litVar l)
  -- hot spot なので汚くても極力 allocation を減らすように
  if litPolarity l
    then return $! m
    else return $! lnot m

varLevel :: Solver -> Var -> IO Level
varLevel s v = do
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

data Solver
  = Solver
  { svOk           :: !(IORef Bool)
  , svVarQueue     :: !(PQ.PriorityQueue IO (Var,VarScore))
  , svAssigned     :: !(IORef (LevelMap [Lit]))
  , svVarCounter   :: !(IORef Int)
  , svVarData      :: !(IORef (V.Vector VarData))
  , svClauseDB     :: !(IORef [SomeConstraint])
  , svLevel        :: !(IORef Level)
  , svBCPQueue     :: !(IORef (Seq.Seq Lit))
  , svModel        :: !(IORef (Maybe (VarMap Bool)))
  , svNDecision    :: !(IORef Int)
  , svNConflict    :: !(IORef Int)
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
assign_ solver lit reason = assert (validLit lit) $ do
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

      when debugMode $ do
        let r = case reason of
                  Nothing -> ""
                  Just _ -> " by propagation"
        debugPrintf "assign(level=%d): %d%s\n" lv lit r

      return True

unassign :: Solver -> Var -> IO ()
unassign solver v = assert (validVar v) $ do
  vd <- varData solver v
  m <- readIORef (vdAssignment vd)
  case m of
    Nothing -> error "should not happen"
    Just a -> do
      writeIORef (vdPolarity vd) (aValue a)
      readIORef (aBacktrackCBs a) >>= sequence_
  writeIORef (vdAssignment vd) Nothing
  score <- varScore solver v
  PQ.enqueue (svVarQueue solver) (v,score)

addBacktrackCB :: Solver -> Var -> IO () -> IO ()
addBacktrackCB solver v callback = do
  vd <- varData solver v
  m <- readIORef (vdAssignment vd)
  case m of
    Nothing -> error "should not happen"
    Just a -> modifyIORef (aBacktrackCBs a) (callback :)

-- | Register the constraint to be notified when the literal becames false.
watch :: Constraint c => Solver -> Lit -> c -> IO ()
watch solver lit c = do
  when debugMode $ do
    lits <- watchedLiterals solver c
    unless (lit `elem` lits) $ error "watch: should not happen"
  ld <- litData solver lit
  modifyIORef (ldWatches ld) (toConstraint c : )

-- | Returns list of constraints that are watching the literal.
watches :: Solver -> Lit -> IO [SomeConstraint]
watches solver lit = do
  ld <- litData solver lit
  readIORef (ldWatches ld)

attachConstraint :: Constraint c => Solver -> c -> IO ()
attachConstraint solver c = do
  modifyIORef (svClauseDB solver) (toConstraint c : )
  str <- showConstraint solver c
  when debugMode $ debugPrintf "constraint %s is added\n" str
  sanityCheck solver

type VarScore = Int

varScore :: Solver -> Var -> IO VarScore
varScore solver !v = do
  vd <- varData solver v
  readIORef (vdScore vd)

incVarScore :: Solver -> Var -> IO ()
incVarScore solver !v = do
  vd <- varData solver v
  modifyIORef' (vdScore vd) (+1)

updateVarQueue :: Solver -> IO ()
updateVarQueue solver = do
  let vqueue = svVarQueue solver
  xs <- PQ.dequeueBatch vqueue
  forM_ xs $ \(v,_) -> do
    score <- varScore solver v
    PQ.enqueue vqueue (v,score)

variables :: Solver -> IO [Var]
variables solver = do
  vcnt <- readIORef (svVarCounter solver)
  return [1 .. vcnt-1]

{--------------------------------------------------------------------
  external API
--------------------------------------------------------------------}

-- | Create a new Solver instance.
newSolver :: IO Solver
newSolver = do
  ok   <- newIORef True
  vcnt <- newIORef 1
  vqueue <- PQ.newPriorityQueue (\(_,score) -> -score)
  assigned <- newIORef IM.empty
  vars <- newIORef V.empty
  db  <- newIORef []
  lv  <- newIORef levelRoot
  q   <- newIORef Seq.empty
  m   <- newIORef Nothing
  ndecision <- newIORef 0
  nconflict <- newIORef 0
  return $
    Solver
    { svOk = ok
    , svVarCounter = vcnt
    , svVarQueue   = vqueue
    , svAssigned   = assigned
    , svVarData    = vars
    , svClauseDB   = db
    , svLevel      = lv
    , svBCPQueue   = q
    , svModel      = m
    , svNDecision  = ndecision
    , svNConflict  = nconflict
    }

-- |Add a new variable
newVar :: Solver -> IO Var
newVar s = do
  v <- readIORef (svVarCounter s)
  writeIORef (svVarCounter s) (v+1)
  PQ.enqueue (svVarQueue s) (v,0)
  vd <- newVarData
  modifyIORef (svVarData s) (\vec -> V.snoc vec vd)
  return v

-- |Add a clause to the solver.
addClause :: Solver -> Clause -> IO ()
addClause solver lits = do
  d <- readIORef (svLevel solver)
  assert (d == levelRoot) $ return ()

  lits <- instantiateClause solver lits
  case normalizeClause =<< lits of
    Nothing -> return ()
    Just [] -> markBad solver
    Just [lit] -> do
      ret <- assign solver lit
      assert ret $ return ()
      ret <- deduce solver
      case ret of
        Nothing -> return ()
        Just _ -> markBad solver
    Just lits'@(l1:l2:_) -> do
      clause <- newClauseData lits'
      watch solver l1 clause
      watch solver l2 clause
      attachConstraint solver clause
      forM_ lits' $ \lit -> incVarScore solver (litVar lit)

-- | Add a cardinality constraints /atleast({l1,l2,..},n)/.
addAtLeast :: Solver -- ^ The 'Solver' argument.
           -> [Lit]  -- ^ set of literals /{l1,l2,..}/ (duplicated elements are ignored)
           -> Int    -- ^ /n/.
           -> IO ()
addAtLeast solver lits n = do
  d <- readIORef (svLevel solver)
  assert (d == levelRoot) $ return ()

  (lits,n) <- instantiateAtLeast solver (lits,n)
  let (lits',n') = normalizeAtLeast (lits,n)
      len = length lits'

  if n' <= 0 then return ()
    else if n' > len then markBad solver
    else if n' == 1 then addClause solver lits'
    else if n' == len then do
      forM_ lits' $ \l -> do
        ret <- assign solver l
        assert ret $ return ()
        ret <- deduce solver
        case ret of
          Nothing -> return ()
          Just _ -> markBad solver
    else do
      c <- newAtLeastData lits' n'
      forM_ (take (n'+1) lits') $ \l -> watch solver l c
      attachConstraint solver c
      forM_ lits $ \lit -> incVarScore solver (litVar lit)

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

  (ts,n) <- instantiatePBAtLeast solver (ts,n)
  let (ts',degree) = normalizePBAtLeast (ts,n)
      cs = map fst ts'
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
        forM_ ts' $ \(_,l) -> do
          watch solver l c
        attachConstraint solver c
        forM_ ts' $ \(_,lit) -> incVarScore solver (litVar lit)

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

-- | Solve constraints.
-- Returns 'True' if the problem is SATISFIABLE.
-- Returns 'False' if the problem is UNSATISFIABLE.
solve :: Solver -> IO Bool
solve solver = do
  debugPrintf "Solving starts ...\n"
  writeIORef (svModel solver) Nothing

  ok <- readIORef (svOk solver)
  if not ok
    then return False
    else do
      when debugMode $ dumpVarScore solver
      updateVarQueue solver
      d <- readIORef (svLevel solver)
      assert (d == levelRoot) $ return ()
      result <- loop
      when result $ do
        when debugMode $ checkSatisfied solver
        constructModel solver
      backtrackTo solver levelRoot
      when debugMode $ dumpVarScore solver
      debugPrintf "#decision = %d\n" =<< readIORef (svNDecision solver)
      debugPrintf "#conflict = %d\n" =<< readIORef (svNConflict solver)
      return result

  where
    loop :: IO Bool
    loop = do
      sanityCheck solver
      conflict <- deduce solver
      sanityCheck solver

      case conflict of
        Nothing -> do
          r <- pickBranchLit solver
          case r of
            Nothing -> return True
            Just lit -> decide solver lit >> loop

        Just constr -> do
          modifyIORef' (svNConflict solver) (+1)
          d <- readIORef (svLevel solver)

          when debugMode $ do
            str <- showConstraint solver constr
            debugPrintf "conflict(level=%d): %s\n" d str

          if d == levelRoot
            then return False
            else do
              learntClause <- analyzeConflict solver constr
              (cl, level, lit) <- newLearntClause solver learntClause
              backtrackTo solver level
              assignBy solver lit cl
              loop

type Model = IM.IntMap Bool

-- | After 'solve' returns True, it returns the model.
model :: Solver -> IO Model
model solver = do
  m <- readIORef (svModel solver)
  return (fromJust m)

{--------------------------------------------------------------------
  API for implementation of @solve@
--------------------------------------------------------------------}

pickBranchLit :: Solver -> IO (Maybe Lit)
pickBranchLit !solver = do
  let vqueue = svVarQueue solver

      loop :: IO (Maybe Var)
      loop = do
        m <- PQ.dequeue vqueue
        case m of
          Nothing -> return Nothing
          Just (var,_) -> do
            val <- varValue solver var
            if val /= lUndef
              then loop
              else do
                vd <- varData solver var
                p <- readIORef (vdPolarity vd)
                let lit = literal var p
                seq lit $ return (Just lit)
  loop

decide :: Solver -> Lit -> IO ()
decide solver lit = do
  modifyIORef' (svNDecision solver) (+1)
  modifyIORef (svLevel solver) (+1)
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
    processLit lit = do
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

analyzeConflict :: Constraint c => Solver -> c -> IO Clause
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

  -- trailを順番に見ていって上手くいくのはbcpQueueが本物のキューだから。
  -- bcpQueueが本物のキューでない場合には、下記のAの箇所で無視した 'litNot l'
  -- が後から必要になることがあり得る。
  let loop :: LitSet -> LitSet -> LitSet -> [Lit] -> IO LitSet
      loop lits1 lits2 seen trail
        | sz==1 = do
            return $ lits1 `IS.union` lits2
        | sz>=2 = do
            case trail of
              [] -> error $ printf "analyzeConflict: should not happen: loop %s %s %s %s"
                              (show lits1) (show lits2) (show seen) (show trail)
              (l:trail') -> do
                if litNot l `IS.notMember` lits1
                 then loop lits1 lits2 seen trail' -- (A)
                 else do
                  let seen' = IS.insert (litNot l) seen
                  m <- varReason solver (litVar l)
                  case m of
                    Nothing -> loop lits1 lits2 seen' trail'
                    Just constr2 -> do
                      xs <- liftM IS.fromList $ reasonOf solver constr2 (Just l)
                      (ys,zs) <- split (IS.toList xs)
                      loop (IS.delete (litNot l) lits1 `IS.union` (ys `IS.difference` seen))
                           (lits2 `IS.union` zs)
                           seen' trail'
        | otherwise = error "analyzeConflict: should not happen"
        where
          sz = IS.size lits1

  conflictClause <- reasonOf solver constr Nothing
  (ys,zs) <- split conflictClause
  trail <- liftM (IM.! d) $ readIORef (svAssigned solver)
  lits <- loop ys zs IS.empty trail

  lits <- minimizeConflictClauseRecursive solver lits

  when debugMode $ do
    let f l = do
          lv <- litLevel solver l
          return $ lv >= d
    litsd <- filterM f (IS.toList lits)
    when (length litsd /= 1) $ do
      xs <- forM (IS.toList lits) $ \l -> do
        lv <- litLevel solver l
        return (l,lv)
      error $ printf "analyzeConflict: not assertive: %s\n" (show xs)

  return $ IS.toList lits

minimizeConflictClauseLocal :: Solver -> LitSet -> IO LitSet
minimizeConflictClauseLocal solver lits = do
  let xs = IS.toAscList lits
  ys <- filterM (liftM not . isRedundant) xs
  when debugMode $ do
    debugPrintf $ "minimizeConflictClauseLocal:\n"
    debugPrint xs
    debugPrint ys
  return $ IS.fromAscList $ ys

  where
    isRedundant :: Lit -> IO Bool
    isRedundant lit = do
      c <- varReason solver (litVar lit)
      case c of
        Nothing -> return False
        Just c -> do
          ls <- reasonOf solver c (Just (litNot lit))
          allM test ls

    test :: Lit -> IO Bool
    test lit = do
      lv <- litLevel solver lit
      return $ lv == levelRoot || lit `IS.member` lits

minimizeConflictClauseRecursive :: Solver -> LitSet -> IO LitSet
minimizeConflictClauseRecursive solver lits = do
  cacheRef <- newIORef IM.empty

  let
    test :: Lit -> IO Bool
    test lit = do
      lv <- litLevel solver lit
      if lv == levelRoot || lit `IS.member` lits
        then return True
        else do
          cache <- readIORef cacheRef
          case IM.lookup lit cache of
            Just b -> return b
            Nothing -> do
              c <- varReason solver (litVar lit)
              case c of
                Nothing -> return False
                Just c -> do
                  ls <- reasonOf solver c (Just (litNot lit))
                  ret <- allM test ls
                  modifyIORef cacheRef (IM.insert lit ret)
                  return ret

    isRedundant :: Lit -> IO Bool
    isRedundant lit = do
      c <- varReason solver (litVar lit)
      case c of
        Nothing -> return False
        Just c -> do
          ls <- reasonOf solver c (Just (litNot lit))
          allM test ls

  let xs = IS.toAscList lits
  ys <- filterM (liftM not . isRedundant) xs
  when debugMode $ do
    debugPrintf $ "minimizeConflictClauseRecursive:\n"
    debugPrint xs
    debugPrint ys
  return $ IS.fromAscList $ ys

-- | Revert to the state at given level
-- (keeping all assignment at @level@ but not beyond).
backtrackTo :: Solver -> Int -> IO ()
backtrackTo solver level = do
  when debugMode $ debugPrintf "backtrackTo: %d\n" level
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
  vds <- readIORef (svVarData solver)
  xs <- forM (zip [1..] (V.toList vds)) $ \(v, vd) -> do
    a <- readIORef (vdAssignment vd)
    return $ (v, aValue (fromJust a))
  let m = IM.fromAscList xs
  writeIORef (svModel solver) (Just m)

newLearntClause :: Solver -> Clause -> IO (ClauseData, Level, Lit)
newLearntClause solver lits = do
  d <- readIORef (svLevel solver)

  xs <- liftM (sortBy (flip (compare `on` snd))) $
    forM lits $ \l -> do
      lv <- litLevel solver l
      return (l,lv)

  let lits2 = map fst xs
      level = head $ filter (< d) (map snd xs ++ [levelRoot])

  cl <- newClauseData lits2
  case lits2 of
    l1:l2:_ -> do
      watch solver l1 cl
      watch solver l2 cl
      attachConstraint solver cl
      forM_ lits2 $ \lit -> incVarScore solver (litVar lit)
    _ -> return ()

  return (cl, level, head lits2)

{--------------------------------------------------------------------
  constraint implementation
--------------------------------------------------------------------}

class Constraint a where
  toConstraint :: a -> SomeConstraint

  showConstraint :: Solver -> a -> IO String

  watchedLiterals :: Solver -> a -> IO [Lit]

  -- | invoked with the watched literal when the literal is falsified.
  propagate :: Solver -> a -> Lit -> IO Bool

  -- | deduce a clause C∨l from the constraint and return C.
  -- C and l should be false and true respectively under the current
  -- assignment.
  basicReasonOf :: Solver -> a -> Maybe Lit -> IO Clause

  isSatisfied :: Solver -> a -> IO Bool

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

  watchedLiterals s (ConstrClause c)    = watchedLiterals s c
  watchedLiterals s (ConstrAtLeast c)   = watchedLiterals s c
  watchedLiterals s (ConstrPBAtLeast c) = watchedLiterals s c

  propagate s (ConstrClause c)  lit   = propagate s c lit
  propagate s (ConstrAtLeast c) lit   = propagate s c lit
  propagate s (ConstrPBAtLeast c) lit = propagate s c lit

  basicReasonOf s (ConstrClause c)  l   = basicReasonOf s c l
  basicReasonOf s (ConstrAtLeast c) l   = basicReasonOf s c l
  basicReasonOf s (ConstrPBAtLeast c) l = basicReasonOf s c l

  isSatisfied s (ConstrClause c)    = isSatisfied s c
  isSatisfied s (ConstrAtLeast c)   = isSatisfied s c
  isSatisfied s (ConstrPBAtLeast c) = isSatisfied s c

{--------------------------------------------------------------------
  Clause
--------------------------------------------------------------------}

newtype ClauseData = ClauseData (IOUArray Int Lit)
  deriving Eq

newClauseData :: Clause -> IO ClauseData
newClauseData ls = do
  let size = length ls
  a <- newListArray (0, size-1) ls
  return (ClauseData a)

instance Constraint ClauseData where
  toConstraint = ConstrClause

  showConstraint _ (ClauseData a) = do
    lits <- getElems a
    return (show lits)

  watchedLiterals _ (ClauseData a) = do
    lits <- getElems a
    case lits of
      l1:l2:_ -> return [l1, l2]
      _ -> return []

  propagate !s this@(ClauseData a) !falsifiedLit = do
    preprocess

    lit0 <- readArray a 0
    val0 <- litValue s lit0
    if val0 == lTrue
      then do
        watch s falsifiedLit this
        return True
      else do
        (!lb,!ub) <- getBounds a
        assert (lb==0) $ return ()
        ret <- findForWatch 2 ub
        case ret of
          Nothing -> do
            when debugMode $ debugPrintf "propagate: %s is unit\n" =<< showConstraint s this
            watch s falsifiedLit this
            assignBy s lit0 this
          Just !i  -> do
            lit1 <- readArray a 1
            liti <- readArray a i
            writeArray a 1 liti
            writeArray a i lit1
            watch s liti this
            return True

    where
      preprocess :: IO ()
      preprocess = do
        l0 <- readArray a 0
        l1 <- readArray a 1
        assert (l0==falsifiedLit || l1==falsifiedLit) $ return ()
        when (l0==falsifiedLit) $ do
          writeArray a 0 l1
          writeArray a 1 l0

      findForWatch :: Int -> Int -> IO (Maybe Int)
      findForWatch i end | i > end = return Nothing
      findForWatch i end = do
        val <- litValue s =<< readArray a i
        if val /= lFalse
          then return (Just i)
          else findForWatch (i+1) end

  basicReasonOf _ (ClauseData a) l = do
    lits <- getElems a
    case l of
      Nothing -> return lits
      Just lit -> do
        assert (lit == head lits) $ return ()
        return $ tail lits

  isSatisfied solver (ClauseData a) = do
    lits <- getElems a
    vals <- mapM (litValue solver) lits
    return $ lTrue `elem` vals

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
  }
  deriving Eq

newAtLeastData :: [Lit] -> Int -> IO AtLeastData
newAtLeastData ls n = do
  let size = length ls
  a <- newListArray (0, size-1) ls
  return (AtLeastData a n)

instance Constraint AtLeastData where
  toConstraint = ConstrAtLeast

  showConstraint _ (AtLeastData a n) = do
    lits <- getElems a
    return $ show lits ++ " >= " ++ show n

  watchedLiterals _ (AtLeastData a n) = do
    lits <- getElems a
    let ws = if length lits > n then take (n+1) lits else []
    return ws

  propagate s this@(AtLeastData a n) falsifiedLit = do
    preprocess

    when debugMode $ do
      litn <- readArray a n
      unless (litn == falsifiedLit) $ error "AtLeastData.propagate: should not happen"

    (lb,ub) <- getBounds a
    assert (lb==0) $ return ()
    ret <- findForWatch (n+1) ub
    case ret of
      Nothing -> do
        when debugMode $ debugPrintf "propagate: %s is unit\n" =<< showConstraint s this
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

  basicReasonOf s (AtLeastData a n) l = do
    lits <- getElems a
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

  isSatisfied solver (AtLeastData a n) = do
    lits <- getElems a
    vals <- mapM (litValue solver) lits
    return $ length [v | v <- vals, v == lTrue] >= n

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
  }
  deriving Eq

newPBAtLeastData :: [(Integer,Lit)] -> Integer -> IO PBAtLeastData
newPBAtLeastData ts degree = do
  let slack = sum (map fst ts) - degree
      m = IM.fromList [(l,c) | (c,l) <- ts]
  s <- newIORef slack
  return (PBAtLeastData m degree s)

instance Constraint PBAtLeastData where
  toConstraint = ConstrPBAtLeast

  showConstraint _ (PBAtLeastData m degree _) = do
    return $ show [(c,l) | (l,c) <- IM.toList m] ++ " >= " ++ show degree

  watchedLiterals _ (PBAtLeastData m _ _) = do
    return $ IM.keys m

  propagate solver this@(PBAtLeastData m _ slack) falsifiedLit = do
    watch solver falsifiedLit this

    let c = m IM.! falsifiedLit
    modifyIORef slack (subtract c)
    addBacktrackCB solver (litVar falsifiedLit) $ modifyIORef slack (+ c)
    s <- readIORef slack

    if s < 0
      then return False
      else if s == 0 then return True
      else do
        let ls = [l1 | (l1,c1) <- IM.toList m, c1 > s]
        when (not (null ls)) $ do
          when debugMode $ do
            str <- showConstraint solver this
            debugPrintf "propagate: %s is unit (new slack = %d)\n" str s
          forM_ ls $ \l1 -> do
            v <- litValue solver l1
            when (v == lUndef) $ do
              assignBy solver l1 this
              return ()
        return True

  basicReasonOf solver (PBAtLeastData m degree _) l = do
    xs <- do
      tmp <- filterM (\(lit,_) -> liftM (lFalse ==) (litValue solver lit)) (IM.toList m)
      return $ sortBy (flip compare `on` snd) tmp
    let max_slack = sum (map snd $ IM.toList m) - degree
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

  isSatisfied solver (PBAtLeastData m degree _) = do
    xs <- forM (IM.toList m) $ \(l,c) -> do
      v <- litValue solver l
      if v == lTrue
        then return c
        else return 0
    return $ sum xs >= degree

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

modifyIORef' :: IORef a -> (a -> a) -> IO ()
modifyIORef' ref f = do
  x <- readIORef ref
  writeIORef ref $! f x

{--------------------------------------------------------------------
  debug
--------------------------------------------------------------------}

debugMode :: Bool
debugMode = False

debugPrintf :: HPrintfType r => String -> r
debugPrintf s = hPrintf stderr ("c " ++ s)

debugPrint :: Show a => a -> IO ()
debugPrint a = hPutStr stderr "c " >> hPrint stderr a

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

dumpVarScore :: Solver -> IO ()
dumpVarScore solver = do
  debugPrintf "Variable scores:\n"
  vs <- variables solver
  forM_ vs $ \v -> do
    score <- varScore solver v
    debugPrintf "score(%d) = %d\n" v score

{--------------------------------------------------------------------
  test
--------------------------------------------------------------------}

-- should be SAT
test1 :: IO ()
test1 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [literal x1 True,  literal x2 True]  -- x1 or x2
  addClause solver [literal x1 True,  literal x2 False] -- x1 or not x2
  addClause solver [literal x1 False, literal x2 False] -- not x1 or not x2
  print =<< solve solver

-- shuld be UNSAT
test2 :: IO ()
test2 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [literal x1 True,  literal x2 True]  -- x1 or x2
  addClause solver [literal x1 False, literal x2 True]  -- not x1 or x2
  addClause solver [literal x1 True,  literal x2 False] -- x1 or not x2
  addClause solver [literal x1 False, literal x2 False] -- not x2 or not x2
  print =<< solve solver

-- top level でいきなり矛盾
test3 :: IO ()
test3 = do
  solver <- newSolver
  x1 <- newVar solver
  addClause solver [literal x1 True]
  addClause solver [literal x1 False]
  print =<< solve solver -- unsat

-- incremental に制約を追加
test4 :: IO ()
test4 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [literal x1 True,  literal x2 True]  -- x1 or x2
  addClause solver [literal x1 True,  literal x2 False] -- x1 or not x2
  addClause solver [literal x1 False, literal x2 False] -- not x1 or not x2
  print =<< solve solver -- sat
  addClause solver [literal x1 False, literal x2 True]  -- not x1 or x2
  print =<< solve solver -- unsat

testAtLeast1 :: IO ()
testAtLeast1 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  addAtLeast solver [x1,x2,x3] 2
  addAtLeast solver [-x1,-x2,-x3] 2
  print =<< solve solver -- unsat

testAtLeast2 :: IO ()
testAtLeast2 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver
  addAtLeast solver [x1,x2,x3,x4] 2
  addClause solver [-x1,-x2]
  addClause solver [-x1,-x3]
  print =<< solve solver

-- from http://www.cril.univ-artois.fr/PB11/format.pdf
testPB1 :: IO ()
testPB1 = do
  solver <- newSolver

  x1 <- newVar solver
  x2 <- newVar solver
  x3 <- newVar solver
  x4 <- newVar solver
  x5 <- newVar solver

  addPBAtLeast solver [(1,x1),(4,x2),(-2,x5)] 2
  addPBAtLeast solver [(-1,x1),(4,x2),(-2,x5)] 3
  addPBAtLeast solver [(12345678901234567890,x4),(4,x3)] 10
  addPBExactly solver [(2,x2),(3,x4),(2,x1),(3,x5)] 5

  print =<< solve solver
