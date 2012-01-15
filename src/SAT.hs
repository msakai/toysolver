module SAT
  ( Var
  , Lit
  , literal
  , litNot
  , litVar
  , litPolarity
  , Clause
  , Solver
  , newSolver
  , newVar
  , addClause
  , solve
  , model
  ) where

import Control.Monad
import Control.Exception
import Data.Array
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

type Var = Int
type VarSet = IS.IntSet
type VarMap = IM.IntMap

validVar :: Var -> Bool
validVar v = v > 0

varIdx :: Var -> Int
varIdx v = assert (validVar v) $ v - 1

type Lit = Int
type LitSet = IS.IntSet

validLit :: Lit -> Bool
validLit l = l /= 0

literal :: Var -> Bool -> Lit
literal v polarity =
  assert (validVar v) $ if polarity then v else litNot v

litNot :: Lit -> Lit
litNot l = assert (validLit l) $ negate l

litVar :: Lit -> Var
litVar l = assert (validLit l) $ abs l

litPolarity :: Lit -> Bool
litPolarity l = assert (validLit l) $ l > 0

litIdx :: Lit -> Int
litIdx l =
  assert (validLit l) $ 
    2 * varIdx (litVar l) + (if litPolarity l then 0 else 1)

type Clause = [Lit]

-- | Normalizing clause
-- 
-- @Nothing@ if the clause is trivially true.
normalizeClause :: Clause -> Maybe Clause
normalizeClause xs =
  if IS.null (IS.intersection ys (IS.map litNot ys))
    then Just (IS.toList ys)
    else Nothing
  where
    ys = IS.fromList xs

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
  , aReason :: !(Maybe ClauseData)
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
    ldWatchers :: !(IORef [ClauseData])
  }

newVarData :: IO VarData
newVarData = do
  assign <- newIORef Nothing
  pos <- newLitData
  neg <- newLitData
  return $ VarData assign pos neg

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

varIsAssigned :: Solver -> Var -> IO Bool
varIsAssigned s l = do
  vd <- varData s (litVar l)
  m <- readIORef (vdAssignment vd)
  return $! isJust m

litIsAssigned :: Solver -> Var -> IO Bool
litIsAssigned s l = varIsAssigned s (litVar l)

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

varReason :: Solver -> Var -> IO (Maybe ClauseData)
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
  , svClauseDB     :: !(IORef [ClauseData])
  , svLevel        :: !(IORef Level)
  , svBCPQueue     :: !(IORef [Lit])
  , svModel        :: !(IORef (Maybe (VarMap Bool)))
  }

bcpEnqueue :: Solver -> Lit -> IO ()
bcpEnqueue solver l = modifyIORef (svBCPQueue solver) (l:)

bcpDequeue :: Solver -> IO (Maybe Lit)
bcpDequeue solver = do
  let ref = svBCPQueue solver
  ls <- readIORef ref
  case ls of
    [] -> return Nothing
    (l:ls) -> do
      writeIORef ref ls
      return (Just l)

assign :: Solver -> Lit -> Maybe ClauseData -> IO ()
assign solver lit reason = assert (validLit lit) $ do
  lv <- case reason of
          Nothing -> readIORef (svLevel solver)
          Just clause -> do
            lits <- getElems (unClauseData clause)
            lvs <- forM lits $ \l ->
              if l==lit then return (-1) else litLevel solver l
            return (maximum lvs)

  vd <- varData solver (litVar lit)

  a' <- readIORef (vdAssignment vd)
  assert (isNothing a') $ return ()

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
         Nothing -> return Nothing
         Just a -> do
           lits <- getElems (unClauseData a)
           return $ Just lits
  debugPrintf "assign(level=%d): %d by %s\n" lv lit (show r)

unassign :: Solver -> Var -> IO ()
unassign solver v = assert (validVar v) $ do
  vd <- varData solver v
  a <- readIORef (vdAssignment vd)
  assert (isJust a) $ return ()
  writeIORef (vdAssignment vd) Nothing
  modifyIORef (svUnassigned solver) (IS.insert v)

watch :: Solver -> Lit -> ClauseData -> IO ()
watch solver lit cl = do
  lits <- getElems (unClauseData cl)
  assert (litNot lit `elem` lits) $ return ()
  ld <- litData solver lit
  modifyIORef (ldWatchers ld) (cl:)

watches :: Solver -> Lit -> IO [ClauseData]
watches s lit = do
  ld <- litData s lit
  readIORef (ldWatchers ld)

{--------------------------------------------------------------------
  external API
--------------------------------------------------------------------}

newSolver :: IO Solver
newSolver = do
  ok   <- newIORef True
  vcnt <- newIORef 1
  unassigned <- newIORef IS.empty
  assigned <- newIORef IM.empty
  vars <- newIORef IM.empty
  db  <- newIORef []
  lv  <- newIORef (-1)
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

newVar :: Solver -> IO Var
newVar s = do
  v <- readIORef (svVarCounter s)
  writeIORef (svVarCounter s) (v+1)
  modifyIORef (svUnassigned s) (IS.insert v)
  vd <- newVarData
  modifyIORef (svVarData s) (IM.insert v vd)
  return v

addClause :: Solver -> Clause -> IO ()
addClause solver lits = do
  case normalizeClause lits of
    Nothing -> return ()
    Just [] -> writeIORef (svOk solver) False
    Just [lit] -> assign solver lit Nothing
    Just lits@(l1:l2:_) -> do
      clause <- newClauseData lits
      watch solver (litNot l1) clause
      watch solver (litNot l2) clause
      modifyIORef (svClauseDB solver) (clause:)

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
        constructModel solver
        m <- model solver
        debugPrint m
      return result

  where
   
    loop :: IO Bool
    loop = do
      conflict <- deduce solver
      case conflict of
        Nothing -> do
          r <- pickBranchLit solver
          case r of
            Nothing -> return True
            Just lit -> decide solver lit >> loop

        Just wlclause -> do
          d <- readIORef (svLevel solver)

          -- debug
          m <- readIORef (svAssigned solver)
          lits <- getElems (unClauseData wlclause)
          debugPrintf "conflict(level=%d): %s\n" d (show lits)

          if d == levelRoot
            then return False
            else do
              (level, learnedClause) <- analyzeConflict solver wlclause
              debugPrintf "leaned clause: %s\n" (show learnedClause)
              backtrackTo solver level
              let lit = head learnedClause
              x <- litIsAssigned solver lit
              assert (not x) $ return ()
              case learnedClause of
                [_] -> assign solver lit Nothing
                l1:l2:_ -> do
                  cl <- newClauseData learnedClause
                  watch solver (litNot l1) cl
                  watch solver (litNot l2) cl
                  modifyIORef (svClauseDB solver) (cl:)
                  assign solver lit (Just cl)
              loop

model :: Solver -> IO (VarMap Bool)
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
  assign solver lit Nothing

deduce :: Solver -> IO (Maybe ClauseData)
deduce solver = loop
  where
    loop :: IO (Maybe ClauseData)
    loop = do
      r <- bcpDequeue solver
      case r of
        Nothing -> return Nothing
        Just lit -> do
          ret <- processLit lit
          case ret of
            Just _ -> return ret
            Nothing -> loop

    processLit :: Lit -> IO (Maybe ClauseData)
    processLit lit = do
      ld <- litData solver lit
      let wsref = ldWatchers ld
      let loop2 [] = return Nothing
          loop2 (w:ws) = do
            ok <- propagate solver w lit
            if ok
              then loop2 ws
              else do
                modifyIORef wsref (++ws)
                return (Just w)
      ws <- readIORef wsref
      loop2 ws

analyzeConflict :: Solver -> ClauseData -> IO (Level, Clause)
analyzeConflict solver clause = do
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
                    Just c -> do
                      lits3 <- getElems (unClauseData c)
                      let xs = IS.delete l $ IS.fromList lits3
                      (ys,zs) <- split (IS.toList (xs `IS.difference` seen))
                      loop (IS.delete (litNot l) lits1 `IS.union` ys)
                           (lits2 `IS.union` zs)
                           (seen `IS.union` xs) trail'
        | otherwise = error "analyzeConflict: should not happen"
        where
          sz = IS.size lits1

  xs <- getElems (unClauseData clause)
  (ys,zs) <- split xs
  trail <- liftM (IM.! d) $ readIORef (svAssigned solver)
  lits <- loop ys zs (IS.fromList xs) trail

  let lits2 = IS.toList lits
  xs <- liftM (sortBy (flip (compare `on` snd))) $
    forM lits2 $ \l -> do
      lv <- litLevel solver l
      return (l, lv)
  let lits3 = map fst xs
  case xs of
    [] -> error "analyzeConflict: should not happen (2)"
    [_] -> return (levelRoot, lits3)
    (_,lv1):(_,_):_ -> do
      debugPrintf "analyzeConflict: %s\n" (show xs)
      assert (lv1==d) $ return ()
      let lv2 = head $ filter (< d) (map snd xs ++ [-1])
      return (lv2, lits3)

-- | Revert to the state at given level
-- (keeping all assignment at 'level' but not beyond).
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
  writeIORef (svModel solver) (Just (IM.fromAscList xs))

assertLearnedClause :: Solver -> ClauseData -> IO ()
assertLearnedClause solver clause = undefined

{--------------------------------------------------------------------
  constraint implementation
--------------------------------------------------------------------}

class Constraint a where
  propagate :: Solver -> a -> Lit -> IO Bool

newtype ClauseData = ClauseData{ unClauseData :: IOUArray Int Lit }

instance Constraint ClauseData where
  propagate s cs lit = do
    preprocess

    lits <- getElems (unClauseData cs)
    debugPrintf "propagating %d to clause %s\n" lit (show lits)

    lit0 <- readArray a 0
    val0 <- litValue s lit0
    if val0 == Just True
      then do
        -- already satisfied!
        debugPrintf "propagate: already satisfied\n"
        watch s lit cs
        return True 
      else do
        (_,ub) <- getBounds a
        ret <- findForWatch 2 ub
        case ret of
          Nothing | val0 == Just False -> do
            -- conflict
            debugPrintf "propagate: conflict\n"
            watch s lit cs
            return False
          Nothing -> do
            -- unit
            debugPrintf "propagate: unit\n"
            assign s lit0 (Just cs)
            watch s lit cs
            return True
          Just i  -> do
            debugPrintf "propagate: watch found\n"
            lit1 <- readArray a 1
            liti <- readArray a i
            writeArray a 1 liti
            writeArray a i lit1
            watch s (litNot liti) cs
            return True

    where
      falsifiedLit = litNot lit

      a = unClauseData cs

      preprocess :: IO ()
      preprocess = do
        l0 <- readArray a 0
        l1 <- readArray a 1
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

newClauseData :: Clause -> IO ClauseData
newClauseData ls = do
  let size = length ls
  a <- newListArray (0, size-1) ls
  return (ClauseData a)

{--------------------------------------------------------------------
  debug
--------------------------------------------------------------------}

debugPrintf :: HPrintfType r => String -> r
debugPrintf s = hPrintf stderr ("c " ++ s) 

debugPrint :: Show a => a -> IO ()
debugPrint a = hPutStr stderr "c " >> hPrint stderr a

{--------------------------------------------------------------------
  test
--------------------------------------------------------------------}

-- should be SAT
test1 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [literal x1 True,  literal x2 True]  -- x1 or x2
  addClause solver [literal x1 True,  literal x2 False] -- x1 or not x2
  addClause solver [literal x1 False, literal x2 False] -- not x1 or not x2
  print =<< solve solver

-- shuld be UNSAT
test2 = do
  solver <- newSolver
  x1 <- newVar solver
  x2 <- newVar solver
  addClause solver [literal x1 True,  literal x2 True]  -- x1 or x2
  addClause solver [literal x1 False, literal x2 True]  -- not x1 or x2
  addClause solver [literal x1 True,  literal x2 False] -- x1 or not x2
  addClause solver [literal x1 False, literal x2 False] -- not x2 or not x2
  print =<< solve solver
