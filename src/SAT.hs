{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}
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
    ldWatches :: !(IORef [ClauseData])
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
    (l:ls') -> do
      writeIORef ref ls'
      return (Just l)

assign :: Solver -> Lit -> Maybe ClauseData -> IO Bool
assign solver lit reason = assert (validLit lit) $ do
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
watch :: Solver -> Lit -> ClauseData -> IO ()
watch solver lit cl = do
  lits <- watchedLiterals solver cl
  assert (lit `elem` lits) $ return ()
  ld <- litData solver lit
  modifyIORef (ldWatches ld) (cl:)

-- | Returns list of constraints that are watching the literal.
watches :: Solver -> Lit -> IO [ClauseData]
watches solver lit = do
  ld <- litData solver lit
  readIORef (ldWatches ld)

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
  d <- readIORef (svLevel solver)
  assert (d == levelRoot) $ return ()

  case normalizeClause lits of
    Nothing -> return ()
    Just [] -> writeIORef (svOk solver) False
    Just [lit] -> do
      ret <- assign solver lit Nothing
      unless ret $ writeIORef (svOk solver) False
    Just lits'@(l1:l2:_) -> do
      clause <- newClauseData lits'
      watch solver l1 clause
      watch solver l2 clause
      modifyIORef (svClauseDB solver) (clause:)
      sanityCheck solver

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
  val <- litValue solver lit
  assert (isNothing val) $ return ()
  assign solver lit Nothing
  return ()

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
  modifyIORef (svClauseDB solver) (cl:)
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
  showConstraint :: Solver -> a -> IO String

  watchedLiterals :: Solver -> a -> IO [Lit]

  -- | invoked with the watched literal when the literal is falsified.
  propagate :: Solver -> a -> Lit -> IO Bool

  -- | deduce a clause C∨l from the constraint and return C.
  -- C and l should be false and true respectively under the current
  -- assignment.
  reasonOf :: Solver -> a -> Maybe Lit -> IO Clause

{--------------------------------------------------------------------
  Clause
--------------------------------------------------------------------}

newtype ClauseData = ClauseData{ unClauseData :: IOUArray Int Lit }

newClauseData :: Clause -> IO ClauseData
newClauseData ls = do
  let size = length ls
  a <- newListArray (0, size-1) ls
  return (ClauseData a)

instance Constraint ClauseData where
  showConstraint _ cs = do
    lits <- getElems (unClauseData cs)
    return (show lits)

  watchedLiterals _ cs = do
    lits <- getElems (unClauseData cs)
    case lits of
      l1:l2:_ -> return [l1, l2]
      _ -> return []

  propagate s cs falsifiedLit = do
    preprocess

    lits <- getElems a
    debugPrintf "propagating %d to clause %s\n" (litNot falsifiedLit) (show lits)

    lit0 <- readArray a 0
    val0 <- litValue s lit0
    if val0 == Just True
      then do
        debugPrintf "propagate: already satisfied\n"
        watch s falsifiedLit cs
        return True 
      else do
        (lb,ub) <- getBounds a
        assert (lb==0) $ return ()
        ret <- findForWatch 2 ub
        case ret of
          Nothing -> do
            debugPrintf "propagate: unit or conflict\n"
            watch s falsifiedLit cs
            assign s lit0 (Just cs)
          Just i  -> do
            debugPrintf "propagate: watch updated\n"
            lit1 <- readArray a 1
            liti <- readArray a i
            writeArray a 1 liti
            writeArray a i lit1
            watch s liti cs
            return True

    where
      a = unClauseData cs

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

  reasonOf _ cs l = do
    lits <- getElems (unClauseData cs)
    case l of
      Nothing -> return lits
      Just lit -> do
        assert (lit == head lits) $ return ()
        return $ tail lits

{-
TODO:
* cardinality constraint
* PB constraint
* XOR clause
-}

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
  xs <- forM cls $ \clause -> do
    let a = unClauseData clause
    lits <- getElems a
    vals <- mapM (litValue solver) lits
    return $ Just True `elem` vals
  assert (and xs) $ return ()

sanityCheck :: Solver -> IO ()
sanityCheck _ | not debugMode = return ()
sanityCheck solver = do
  cls <- readIORef (svClauseDB solver)
  forM_ cls $ \constr -> do
    let a = unClauseData constr
    lits <- watchedLiterals solver constr
    forM_ lits $ \l -> do
      ws <- liftM (map unClauseData) $ watches solver l
      unless (a `elem` ws) $ error $ printf "sanityCheck:A:%s" (show lits)

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
