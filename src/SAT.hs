{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
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
-- * PB constraint
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

  -- * Solving
  , solve

--  -- * Read state

  -- * Extract results
  , Model
  , model
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
import System.IO
import Text.Printf

{--------------------------------------------------------------------
  pure/persistent data structures
--------------------------------------------------------------------}

-- | Variable is represented as positive integers (DIMACS format).
type Var = Int

type VarSet = IS.IntSet
type VarMap = IM.IntMap

validVar :: Var -> Bool
validVar v = v > 0

-- | Positive (resp. negative) literals are represented as positive (resp.
-- negative) integers. (DIMACS format).
type Lit = Int

type LitSet = IS.IntSet

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

-- | Underlying variable of the 'Lit'
litVar :: Lit -> Var
litVar l = assert (validLit l) $ abs l

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
  }

data VarData
  = VarData
  { vdAssignment :: !(IORef (Maybe Assignment))
  , vdPosLitData :: !LitData
  , vdNegLitData :: !LitData
  }

data LitData
  = LitData
  { -- | will be invoked when this literal is falsified
    ldWatches :: !(IORef [SomeConstraint])
  }

newVarData :: IO VarData
newVarData = do
  ainfo <- newIORef Nothing
  pos <- newLitData
  neg <- newLitData
  return $ VarData ainfo pos neg

newLitData :: IO LitData
newLitData = do
  ws <- newIORef []
  return $ LitData ws

varData :: Solver -> Var -> IO VarData
varData s v = do
  m <- readIORef (svVarData s)
  return $! m IM.! v

litData :: Solver -> Lit -> IO LitData
litData s l = do
  vd <- varData s (litVar l)
  return $!
    if litPolarity l
    then vdPosLitData vd
    else vdNegLitData vd

varValue :: Solver -> Var -> IO (Maybe Bool)
varValue s v = do
  vd <- varData s v
  m <- readIORef (vdAssignment vd)
  return $ fmap aValue m

litValue :: Solver -> Lit -> IO (Maybe Bool)
litValue s l = do
  m <- varValue s (litVar l)
  return $ fmap (if litPolarity l then id else not) m

varLevel :: Solver -> Var -> IO Level
varLevel s v = do
  vd <- varData s v
  m <- readIORef (vdAssignment vd)
  case m of
    Nothing -> error "varLevel: unassigned var"
    Just a -> return (aLevel a)

litLevel :: Solver -> Lit -> IO Level
litLevel s l = varLevel s (litVar l)

varReason :: Solver -> Var -> IO (Maybe SomeConstraint)
varReason s v = do
  vd <- varData s v
  m <- readIORef (vdAssignment vd)
  case m of
    Nothing -> error "varReason: unassigned var"
    Just a -> return (aReason a)

data Solver
  = Solver
  { svOk           :: !(IORef Bool)
  , svUnassigned   :: !(IORef VarSet)
  , svAssigned     :: !(IORef (LevelMap [Lit]))
  , svVarCounter   :: !(IORef Int)
  , svVarData      :: !(IORef (VarMap VarData))
  , svClauseDB     :: !(IORef [SomeConstraint])
  , svLevel        :: !(IORef Level)
  , svBCPQueue     :: !(IORef [Lit])
  , svModel        :: !(IORef (Maybe (VarMap Bool)))
  }

markBad :: Solver -> IO ()
markBad solver = writeIORef (svOk solver) False

bcpEnqueue :: Solver -> Lit -> IO ()
bcpEnqueue solver l = modifyIORef (svBCPQueue solver) (l:)

bcpDequeue :: Solver -> IO (Maybe Lit)
bcpDequeue solver = do
  let ref = svBCPQueue solver
  ls <- readIORef ref
  case ls of
    [] -> return Nothing
    (l:ls') -> do
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

      writeIORef (vdAssignment vd) $ Just $
        Assignment
        { aValue  = litPolarity lit
        , aLevel  = lv
        , aReason = reason
        }

      modifyIORef (svAssigned solver) (IM.insertWith (++) lv [lit])
      modifyIORef (svUnassigned solver) (IS.delete (litVar lit))
      bcpEnqueue solver lit

      -- debug
      r <- case reason of
             Nothing -> return ""
             Just constr -> liftM (" by " ++) $ showConstraint solver constr
      debugPrintf "assign(level=%d): %d%s\n" lv lit r

      return True

unassign :: Solver -> Var -> IO ()
unassign solver v = assert (validVar v) $ do
  vd <- varData solver v
  a <- readIORef (vdAssignment vd)
  assert (isJust a) $ return ()
  writeIORef (vdAssignment vd) Nothing
  modifyIORef (svUnassigned solver) (IS.insert v)

-- | Register the constraint to be notified when the literal becames false.
watch :: Constraint c => Solver -> Lit -> c -> IO ()
watch solver lit c = do
  lits <- watchedLiterals solver c
  assert (lit `elem` lits) $ return ()
  ld <- litData solver lit
  modifyIORef (ldWatches ld) (toConstraint c : )

-- | Returns list of constraints that are watching the literal.
watches :: Solver -> Lit -> IO [SomeConstraint]
watches solver lit = do
  ld <- litData solver lit
  readIORef (ldWatches ld)

{--------------------------------------------------------------------
  external API
--------------------------------------------------------------------}

-- | Create a new Solver instance.
newSolver :: IO Solver
newSolver = do
  ok   <- newIORef True
  vcnt <- newIORef 1
  unassigned <- newIORef IS.empty
  assigned <- newIORef IM.empty
  vars <- newIORef IM.empty
  db  <- newIORef []
  lv  <- newIORef levelRoot
  q   <- newIORef []
  m   <- newIORef Nothing
  return $
    Solver
    { svOk = ok
    , svVarCounter = vcnt
    , svUnassigned = unassigned
    , svAssigned   = assigned
    , svVarData    = vars
    , svClauseDB   = db
    , svLevel      = lv
    , svBCPQueue   = q
    , svModel      = m
    }

-- |Add a new variable
newVar :: Solver -> IO Var
newVar s = do
  v <- readIORef (svVarCounter s)
  writeIORef (svVarCounter s) (v+1)
  modifyIORef (svUnassigned s) (IS.insert v)
  vd <- newVarData
  modifyIORef (svVarData s) (IM.insert v vd)
  return v

-- |Add a clause to the solver.
addClause :: Solver -> Clause -> IO ()
addClause solver lits = do
  d <- readIORef (svLevel solver)
  assert (d == levelRoot) $ return ()

  case normalizeClause lits of
    Nothing -> return ()
    Just [] -> markBad solver
    Just [lit] -> do
      ret <- assign solver lit
      unless ret $ markBad solver
    Just lits'@(l1:l2:_) -> do
      clause <- newClauseData lits'
      watch solver l1 clause
      watch solver l2 clause
      modifyIORef (svClauseDB solver) (toConstraint clause : )
      sanityCheck solver

-- | Add a cardinality constraints /atleast({l1,l2,..},n)/.
addAtLeast :: Solver -- ^ The 'Solver' argument.
           -> [Lit]  -- ^ set of literals /{l1,l2,..}/ (duplicated elements are ignored)
           -> Int    -- ^ /n/.
           -> IO ()
addAtLeast solver lits n = do
  d <- readIORef (svLevel solver)
  assert (d == levelRoot) $ return ()

  let (lits',n') = normalizeAtLeast (lits,n)
      len = length lits'

  if n' <= 0 then return ()
    else if n' > len then markBad solver
    else if n' == 1 then addClause solver lits'
    else if n' == len then do
      forM_ lits' $ \l -> do
        ret <- assign solver l
        unless ret $ markBad solver
    else do
      c <- newAtLeastData lits' n'
      forM_ (take (n'+1) lits) $ \l -> watch solver l c
      modifyIORef (svClauseDB solver) (toConstraint c : )
      sanityCheck solver

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

-- | Solve constraints.
-- Returns 'True' if the problem is SATISFIABLE.
-- Returns 'False' if the problem is UNSATISFIABLE.
solve :: Solver -> IO Bool
solve solver = do
  writeIORef (svModel solver) Nothing
  backtrackTo solver levelRoot

  ok <- readIORef (svOk solver)
  if not ok
    then return False
    else do
      lits <- liftM (IM.findWithDefault [] levelRoot) $
        readIORef (svAssigned solver)
      mapM_ (bcpEnqueue solver) lits
      result <- loop
      when result $ do
        when debugMode $ checkSatisfied solver
        constructModel solver
        backtrackTo solver levelRoot
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
          d <- readIORef (svLevel solver)

          -- debug
          str <- showConstraint solver constr
          debugPrintf "conflict(level=%d): %s\n" d str

          if d == levelRoot
            then return False
            else do
              learntClause <- analyzeConflict solver constr
              debugPrintf "learnt clause: %s\n" (show learntClause)
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
pickBranchLit solver = do
  let ref = svUnassigned solver
  vs <- readIORef ref
  case IS.minView vs of
    Nothing -> return Nothing
    Just (v,vs') -> do
      writeIORef ref vs'
      return (Just (literal v True))

decide :: Solver -> Lit -> IO ()
decide solver lit = do
  modifyIORef (svLevel solver) (+1)
  val <- litValue solver lit
  assert (isNothing val) $ return ()
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
            if lv >= d
              then go (IS.insert l xs, ys) ls
              else go (xs, IS.insert l ys) ls

  let loop :: LitSet -> LitSet -> LitSet -> [Lit] -> IO LitSet
      loop lits1 lits2 seen trail
        | sz==1 = do
            return $ lits1 `IS.union` lits2
        | sz>=2 = do
            case trail of
              [] -> return $ lits1 `IS.union` lits2
              (l:trail') ->
                if litNot l `IS.notMember` lits1
                then loop lits1 lits2 seen trail'
                else do
                  m <- varReason solver (litVar l)
                  case m of
                    Nothing -> loop lits1 lits2 seen trail'
                    Just constr2 -> do
                      xs <- liftM IS.fromList $ reasonOf solver constr2 (Just l)
                      (ys,zs) <- split (IS.toList (xs `IS.difference` seen))
                      loop (IS.delete (litNot l) lits1 `IS.union` ys)
                           (lits2 `IS.union` zs)
                           (seen `IS.union` xs) trail'
        | otherwise = error "analyzeConflict: should not happen"
        where
          sz = IS.size lits1

  conflictClause <- reasonOf solver constr Nothing
  (ys,zs) <- split conflictClause
  trail <- liftM (IM.! d) $ readIORef (svAssigned solver)
  lits <- loop ys zs (IS.union ys zs) trail
  return $ IS.toList lits

-- | Revert to the state at given level
-- (keeping all assignment at @level@ but not beyond).
backtrackTo :: Solver -> Int -> IO ()
backtrackTo solver level = do
  debugPrintf "backtrackTo: %d\n" level
  m <- readIORef (svAssigned solver)
  m' <- loop m
  writeIORef (svAssigned solver) m'
  writeIORef (svBCPQueue solver) []
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
  xs <- forM (IM.toAscList vds) $ \(v, vd) -> do
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
  modifyIORef (svClauseDB solver) (toConstraint cl : )
  case lits2 of
    l1:l2:_ -> do
      watch solver l1 cl
      watch solver l2 cl
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
  reasonOf :: Solver -> a -> Maybe Lit -> IO Clause

  isSatisfied :: Solver -> a -> IO Bool

data SomeConstraint
  = ConstrClause !ClauseData
  | ConstrAtLeast !AtLeastData
  deriving Eq

instance Constraint SomeConstraint where
  toConstraint = id

  showConstraint s (ConstrClause c)  = showConstraint s c
  showConstraint s (ConstrAtLeast c) = showConstraint s c

  watchedLiterals s (ConstrClause c)  = watchedLiterals s c
  watchedLiterals s (ConstrAtLeast c) = watchedLiterals s c

  propagate s (ConstrClause c)  lit = propagate s c lit
  propagate s (ConstrAtLeast c) lit = propagate s c lit

  reasonOf s (ConstrClause c)  l = reasonOf s c l
  reasonOf s (ConstrAtLeast c) l = reasonOf s c l

  isSatisfied s (ConstrClause c)  = isSatisfied s c
  isSatisfied s (ConstrAtLeast c) = isSatisfied s c

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

  propagate s this@(ClauseData a) falsifiedLit = do
    preprocess

    lits <- getElems a
    debugPrintf "propagating %d to clause %s\n" (litNot falsifiedLit) (show lits)

    lit0 <- readArray a 0
    val0 <- litValue s lit0
    if val0 == Just True
      then do
        debugPrintf "propagate: already satisfied\n"
        watch s falsifiedLit this
        return True
      else do
        (lb,ub) <- getBounds a
        assert (lb==0) $ return ()
        ret <- findForWatch 2 ub
        case ret of
          Nothing -> do
            debugPrintf "propagate: unit or conflict\n"
            watch s falsifiedLit this
            assignBy s lit0 this
          Just i  -> do
            debugPrintf "propagate: watch updated\n"
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
        if val /= Just False
          then return (Just i)
          else findForWatch (i+1) end

  reasonOf _ (ClauseData a) l = do
    lits <- getElems a
    case l of
      Nothing -> return lits
      Just lit -> do
        assert (lit == head lits) $ return ()
        return $ tail lits

  isSatisfied solver (ClauseData a) = do
    lits <- getElems a
    vals <- mapM (litValue solver) lits
    return $ Just True `elem` vals

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

    str <- showConstraint s this
    debugPrintf "propagating %d to %s\n" (litNot falsifiedLit) str

    (lb,ub) <- getBounds a
    assert (lb==0) $ return ()
    ret <- findForWatch (n+1) ub
    case ret of
      Nothing -> do
        debugPrintf "propagate AtLeast: unit or conflict or satisfied\n"
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
        debugPrintf "propagate AtLeast: watch updated\n"
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
        if val /= Just False
          then return (Just i)
          else findForWatch (i+1) end

  reasonOf _ (AtLeastData a n) l = do
    lits <- getElems a
    case l of
      Nothing -> return $ drop (n-1) lits
      Just lit -> do
        assert (lit `elem` take n lits) $ return ()
        return $ drop n lits

  isSatisfied solver (AtLeastData a n) = do
    lits <- getElems a
    vals <- mapM (litValue solver) lits
    return $ length [v | v <- vals, v == Just True] >= n

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

  m <- readIORef (svVarData solver)
  let lits = [l | v <- IM.keys m, l <- [literal v True, literal v False]]
  forM_ lits $ \l -> do
    cs <- watches solver l
    forM_ cs $ \constr -> do
      lits2 <- watchedLiterals solver constr
      unless (l `elem` lits2) $ do
        error $ printf "sanityCheck:C:%d %s" l (show lits2)

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
