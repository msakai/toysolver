{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.EUF.CongruenceClosure
-- Copyright   :  (c) Masahiro Sakai 2012, 2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (BangPatterns, ScopedTypeVariables)
--
-- References:
--
-- * R. Nieuwenhuis and A. Oliveras, "Fast congruence closure and extensions,"
--   Information and Computation, vol. 205, no. 4, pp. 557-580, Apr. 2007.
--   <http://www.lsi.upc.edu/~oliveras/espai/papers/IC.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.EUF.CongruenceClosure
  (
  -- * The @Solver@ type
    Solver
  , newSolver

  -- * Problem description
  , FSym
  , Term (..)
  , FlatTerm (..)
  , ConstrID
  , newFSym
  , newConst
  , newFuncN
  , merge
  , merge'    
  , mergeFlatTerm
  , mergeFlatTerm'

  -- * Query
  , areCongruent
  , areCongruentFlatTerm

  -- * Explanation
  , explain
  , explainFlatTerm
  , explainConst

  -- * Backtracking
  , pushBacktrackPoint
  , popBacktrackPoint

  -- * Low-level operations
  , termToFlatTerm
  , termToFSym
  , flatTermToFSym
  ) where

import Prelude hiding (lookup)

import Control.Exception (assert)
import Control.Loop
import Control.Monad
import Data.IORef
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Semigroup

import qualified ToySolver.Internal.Data.Vec as Vec
    
type FSym = Int

data Term = TApp FSym [Term]
  deriving (Ord, Eq, Show)

data FlatTerm
  = FTConst !FSym
  | FTApp !FSym !FSym
  deriving (Ord, Eq, Show)

type ConstrID = Int

-- | @Eqn0 cid a b@ represents an equation "a = b"
data Eqn0 = Eqn0 (Maybe ConstrID) !FSym !FSym
  deriving (Eq, Ord, Show)

-- | @Eqn1 cid a b c@ represents an equation "f(a,b) = c"
data Eqn1 = Eqn1 (Maybe ConstrID) !FSym !FSym !FSym
  deriving (Eq, Ord, Show)

-- | An equation @a = b@ represented as either
-- 
-- * @a = b@ or
--
-- * @f(a1,a2) = a, f(b1,b2) = b@ where @a1 = b1@ and @a2 = b2@ has already been derived.
-- 
type Eqn = Either Eqn0 (Eqn1, Eqn1)

data Class
  = ClassSingleton !FSym
  | ClassUnion !Int Class Class
  deriving (Show)

instance Semigroup Class where
  xs <> ys = ClassUnion (classSize xs + classSize ys) xs ys
  stimes = stimesIdempotent

classSize :: Class -> Int
classSize (ClassSingleton _) = 1
classSize (ClassUnion size _ _) = size

-- Use mono-traversable package?
classToList :: Class -> [FSym]
classToList c = f c []
  where
    f (ClassSingleton v) = (v :)
    f (ClassUnion _ xs ys) = f xs . f ys

-- Use mono-traversable package?
classForM_ :: Monad m => Class -> (FSym -> m ()) -> m ()
classForM_ xs f = g xs
  where
    g (ClassSingleton v) = f v
    g (ClassUnion _ xs ys) = g xs >> g ys

data Solver
  = Solver
  { svDefs                 :: !(IORef (IntMap (FSym,FSym), Map (FSym,FSym) FSym))
  , svRepresentativeTable  :: !(Vec.UVec FSym)
  , svClassList            :: !(Vec.Vec Class)
  , svParent               :: !(IORef (IntMap (FSym, Eqn)))
  , svUseList              :: !(IORef (IntMap [(Eqn1, Level, Gen)]))
  , svLookupTable          :: !(IORef (IntMap (IntMap Eqn1)))

  -- workspace for constraint propagation
  , svPending :: !(Vec.Vec Eqn)

  -- workspace for explanation generation
  , svERepresentativeTable :: !(Vec.UVec FSym)
  , svEClassList           :: !(Vec.Vec Class)
  , svEHighestNodeTable    :: !(Vec.UVec FSym)
  , svEPendingProofs       :: !(Vec.Vec (FSym,FSym))

  -- for backtracking
  , svTrail :: !(Vec.Vec [TrailItem])
  , svLevelGen :: !(Vec.UVec Int)
  , svIsAfterBacktracking :: !(IORef Bool)
  }

newSolver :: IO Solver
newSolver = do
  defs     <- newIORef (IntMap.empty, Map.empty)
  rep      <- Vec.new
  classes  <- Vec.new
  parent   <- newIORef IntMap.empty
  useList  <- newIORef IntMap.empty
  lookup   <- newIORef IntMap.empty

  pending  <- Vec.new

  repE     <- Vec.new
  classesE <- Vec.new
  highE    <- Vec.new
  pendingE <- Vec.new

  trail <- Vec.new
  gen <- Vec.new
  Vec.push gen 0
  isAfterBT <- newIORef False
      
  return $
    Solver
    { svDefs                = defs
    , svRepresentativeTable = rep
    , svClassList           = classes
    , svParent              = parent
    , svUseList             = useList
    , svLookupTable         = lookup

    -- workspace for constraint propagation
    , svPending = pending

    -- workspace for explanation generation
    , svERepresentativeTable = repE
    , svEClassList           = classesE
    , svEHighestNodeTable    = highE
    , svEPendingProofs       = pendingE

    -- for backtracking
    , svTrail = trail
    , svLevelGen = gen
    , svIsAfterBacktracking = isAfterBT
    }

getNFSyms :: Solver -> IO Int
getNFSyms solver = Vec.getSize (svRepresentativeTable solver)

newFSym :: Solver -> IO FSym
newFSym solver = do
  v <- getNFSyms solver
  Vec.push (svRepresentativeTable solver) v
  Vec.push (svClassList solver) (ClassSingleton v)
  modifyIORef' (svUseList solver) (IntMap.insert v [])
  Vec.push (svERepresentativeTable solver) v
  Vec.push (svEClassList solver) undefined
  Vec.push (svEHighestNodeTable solver) v
  return v

newConst :: Solver -> IO Term
newConst solver = do
  c <- newFSym solver
  return $ TApp c []

newFuncN :: Solver -> IO ([Term] -> Term)
newFuncN solver = do
  c <- newFSym solver
  return $ TApp c

merge :: Solver -> Term -> Term -> IO ()
merge solver t u = merge' solver t u Nothing

merge' :: Solver -> Term -> Term -> Maybe ConstrID -> IO ()
merge' solver t u cid = do
  t' <- termToFlatTerm solver t
  u' <- termToFlatTerm solver u
  case (t', u') of
    (FTConst c, _) -> mergeFlatTerm' solver u' c cid
    (_, FTConst c) -> mergeFlatTerm' solver t' c cid
    _ -> do
      c <- flatTermToFSym solver u'
      mergeFlatTerm' solver t' c cid

mergeFlatTerm :: Solver -> FlatTerm -> FSym -> IO ()
mergeFlatTerm solver s a = mergeFlatTerm' solver s a Nothing

mergeFlatTerm' :: Solver -> FlatTerm -> FSym -> Maybe ConstrID -> IO ()
mergeFlatTerm' solver s a cid = do
  initAfterBacktracking solver
  case s of
    FTConst c -> do
      let eq1 = Eqn0 cid c a
      addToPending solver (Left eq1)
      propagate solver
      checkInvariant solver
    FTApp a1 a2 -> do
      let eq1 = Eqn1 cid a1 a2 a
      a1' <- getRepresentative solver a1
      a2' <- getRepresentative solver a2
      ret <- lookup solver a1' a2'
      case ret of
        Just eq2 -> do
          addToPending solver $ Right (eq1, eq2)
          propagate solver
          checkInvariant solver
        Nothing -> do          
          setLookup solver a1' a2' eq1
          lv <- getCurrentLevel solver
          gen <- getLevelGen solver lv
          modifyIORef' (svUseList solver) $
            IntMap.adjust ((eq1, lv, gen) :) a1' .
            IntMap.adjust ((eq1, lv, gen) :) a2'
          checkInvariant solver

propagate :: Solver -> IO ()
propagate solver = go
  where
    go = do
      checkInvariant solver
      n <- Vec.getSize (svPending solver)
      unless (n == 0) $ do
        processEqn =<< Vec.unsafePop (svPending solver)
        go

    processEqn p = do
      let (a,b) = case p of
                    Left (Eqn0 _ a b) -> (a,b)
                    Right (Eqn1 _ _ _ a, Eqn1 _ _ _ b) -> (a,b)
      a' <- getRepresentative solver a
      b' <- getRepresentative solver b
      unless (a' == b') $ do
        classA <- Vec.unsafeRead (svClassList  solver) a'
        classB <- Vec.unsafeRead (svClassList  solver) b'
        (a,b,a',b',classA,classB) <- return $
          if classSize classA < classSize classB then
            (a,b,a',b',classA,classB)
          else
            (b,a,b',a',classB,classA)
        origRootA <- updateParent a b p
        update a' b' classA classB
        addToTrail solver (TrailMerge a' b' a origRootA)

    update a' b' classA classB = do
      classForM_ classA $ \c -> do
        Vec.unsafeWrite (svRepresentativeTable solver) c b'
      Vec.unsafeWrite (svClassList solver) b' (classA <> classB)

      lv <- getCurrentLevel solver
      lv_gen <- getLevelGen solver lv
      useList <- readIORef (svUseList solver)
      useList_a' <- flip filterM (useList IntMap.! a') $ \(eq1@(Eqn1 _ c1 c2 _), lv2, lv2_gen2) -> do
        lv2_gen <- getLevelGen solver lv2
        if lv2 <= lv && lv2_gen2 == lv2_gen then do
          c1' <- getRepresentative solver c1
          c2' <- getRepresentative solver c2
          assert (b' == c1' || b' == c2') $ return ()
          -- unless (b' == c1' || b' == c2') $ error "ToySolver.EUF.CongruenceClosure.propagate.update: should not happen"
          ret <- lookup solver c1' c2'
          case ret of
            Just eq2 -> do
              addToPending solver $ Right (eq1, eq2)
            Nothing -> do
              setLookup solver c1' c2' eq1
              modifyIORef (svUseList solver) $ IntMap.adjust ((eq1, lv, lv_gen) :) b'
              return ()
          return True
        else do
          -- out-of-date entry
          return False
      modifyIORef' (svUseList solver) (IntMap.insert a' useList_a')

    -- Insert edge a→b labelled with a_eq_b into the proof forest, and re-orient its original ancestors.
    updateParent a b a_eq_b = do
      let loop d (c, c_eq_d) = do
            tbl <- readIORef (svParent solver)
            writeIORef (svParent solver) (IntMap.insert d (c, c_eq_d) tbl)
            case IntMap.lookup d tbl of
              Nothing -> return d
              Just (e, d_eq_e) -> loop e (d, d_eq_e)
      loop a (b, a_eq_b)

areCongruent :: Solver -> Term -> Term -> IO Bool
areCongruent solver t1 t2 = do
  u1 <- termToFlatTerm solver t1
  u2 <- termToFlatTerm solver t2
  areCongruentFlatTerm solver u1 u2

areCongruentFlatTerm :: Solver -> FlatTerm -> FlatTerm -> IO Bool
areCongruentFlatTerm solver t1 t2 = do
  initAfterBacktracking solver
  u1 <- normalize solver t1
  u2 <- normalize solver t2
  return $ u1 == u2

normalize :: Solver -> FlatTerm -> IO FlatTerm
normalize solver (FTConst c) = liftM FTConst $ getRepresentative solver c
normalize solver (FTApp t1 t2) = do
  u1 <- getRepresentative solver t1
  u2 <- getRepresentative solver t2
  ret <- lookup solver u1 u2
  case ret of
    Just (Eqn1 _ _ _ a) -> liftM FTConst $ getRepresentative solver a
    Nothing -> return $ FTApp u1 u2

checkInvariant :: Solver -> IO ()
checkInvariant _ | True = return ()
checkInvariant solver = do
  nv <- getNFSyms solver

  representatives <- liftM IntSet.fromList $ Vec.getElems (svRepresentativeTable solver)

  ref <- newIORef IntSet.empty          
  forM_ (IntSet.toList representatives) $ \a' -> do
    bs <- Vec.read (svClassList solver) a'
    forM_ (classToList bs) $ \b -> do
      b' <- getRepresentative solver b
      unless (a' == b') $
        error "ToySolver.EUF.CongruenceClosure.checkInvariant: inconsistency between classList and representativeTable"
      modifyIORef' ref (IntSet.insert b)

  xs <- readIORef ref
  unless (xs == IntSet.fromList [0..nv-1]) $
    error "ToySolver.EUF.CongruenceClosure.checkInvariant: classList is not exhaustive"

  pendings <- Vec.getElems (svPending solver)
  forM_ pendings $ \p -> do
    case p of
      Left _ -> return ()
      Right (Eqn1 _ a1 a2 _, Eqn1 _ b1 b2 _) -> do
        a1' <- getRepresentative solver a1
        a2' <- getRepresentative solver a2
        b1' <- getRepresentative solver b1
        b2' <- getRepresentative solver b2
        unless (a1' == b1' && a2' == b2') $
          error "ToySolver.EUF.CongruenceClosure.checkInvariant: error in pendingList"

  useList <- readIORef (svUseList solver)
  lv <- getCurrentLevel solver
  forM_ (IntSet.toList representatives) $ \a -> do
    forM_ (useList IntMap.! a) $ \(Eqn1 _ b1 b2 _, lv2, lv2_gen2) -> do
      lv2_gen <- getLevelGen solver lv2
      when (lv2 <= lv && lv2_gen2 == lv2_gen) $ do
        b1' <- getRepresentative solver b1
        b2' <- getRepresentative solver b2
        unless (a == b1' || a == b2') $
          error "ToySolver.EUF.CongruenceClosure.checkInvariant: error in useList"

  forM_ (IntSet.toList representatives) $ \b -> do
    forM_ (IntSet.toList representatives) $ \c -> do
      m <- lookup solver b c
      case m of
        Nothing -> return ()
        Just (Eqn1 _ a1 a2 _) -> do
          a1' <- getRepresentative solver a1
          a2' <- getRepresentative solver a2
          unless (b == a1' && c == a2') $
            error "ToySolver.EUF.CongruenceClosure.checkInvariant: error in lookupTable"

explain :: Solver -> Term -> Term -> IO (Maybe IntSet)
explain solver t1 t2 = do
  c1 <- termToFlatTerm solver t1
  c2 <- termToFlatTerm solver t2
  explainFlatTerm solver c1 c2

explainFlatTerm :: Solver -> FlatTerm -> FlatTerm -> IO (Maybe IntSet)
explainFlatTerm solver t1 t2 = do
  c1 <- flatTermToFSym solver t1
  c2 <- flatTermToFSym solver t2
  explainConst solver c1 c2

explainConst :: Solver -> FSym -> FSym -> IO (Maybe IntSet)
explainConst solver c1 c2 = do
  initAfterBacktracking solver
  n <- getNFSyms solver
  
  -- Additional union-find data structure
  forLoop 0 (<n) (+1) $ \a -> do
    Vec.unsafeWrite (svERepresentativeTable solver) a a
    Vec.unsafeWrite (svEClassList solver) a (ClassSingleton a)
    Vec.unsafeWrite (svEHighestNodeTable solver) a a
                
  let getRepresentative2 :: FSym -> IO FSym
      getRepresentative2 a = Vec.unsafeRead (svERepresentativeTable solver) a

      highestNode :: FSym -> IO FSym
      highestNode c = do
        d <- getRepresentative2 c
        Vec.unsafeRead (svEHighestNodeTable solver) d

      union :: FSym -> FSym -> IO ()
      union a b = do
        a' <- getRepresentative2 a
        b' <- getRepresentative2 b
        classA <- Vec.unsafeRead (svEClassList solver) a'
        classB <- Vec.unsafeRead (svEClassList solver) b'
        h <- highestNode b'
        (a', b', classA, classB) <-
          if classSize classA < classSize classB then do
            return (a', b', classA, classB)
          else
            return (b', a', classB, classA)
        classForM_ classA $ \c -> do
          Vec.unsafeWrite (svERepresentativeTable solver) c b'
        Vec.unsafeWrite (svEClassList solver) b' (classA <> classB)
        Vec.unsafeWrite (svEHighestNodeTable solver) b' h

  Vec.clear (svEPendingProofs solver)
  Vec.push (svEPendingProofs solver) (c1,c2)
  result <- newIORef IntSet.empty

  let loop = do
        n <- Vec.getSize (svEPendingProofs solver)
        if n == 0 then
          return True
        else do
          (a,b) <- Vec.unsafePop (svEPendingProofs solver)
          m <- nearestCommonAncestor solver a b
          case m of
            Nothing -> return False
            Just c -> do
              explainAlongPath a c
              explainAlongPath b c
              loop

      explainAlongPath :: FSym -> FSym -> IO ()
      explainAlongPath a c = do
        a <- highestNode a
        -- note that c is already @highestNode c@
        let loop a =
              unless (a == c) $ do
                Just (b, eq) <- getParent solver a
                case eq of
                  Left (Eqn0 cid _ _) -> do
                    modifyIORef' result (maybeToIntSet cid <>)
                  Right (Eqn1 cid1 a1 a2 _, Eqn1 cid2 b1 b2 _) -> do
                    modifyIORef' result ((maybeToIntSet cid1 <> maybeToIntSet cid2) <>)
                    Vec.push (svEPendingProofs solver) (a1,b1)
                    Vec.push (svEPendingProofs solver) (a2,b2)
                union a b
                loop =<< highestNode b
        loop a

  b <- loop
  if b
  then liftM Just $ readIORef result
  else return Nothing

-- -------------------------------------------------------------------
-- Backtracking
-- -------------------------------------------------------------------

type Level = Int
type Gen = Int

data TrailItem
  = TrailMerge !FSym !FSym !FSym !FSym
  | TrailSetLookup !FSym !FSym
  deriving (Show)

addToTrail :: Solver -> TrailItem -> IO ()
addToTrail solver item = do
  lv <- getCurrentLevel solver
  when (lv /= 0) $ do
    xs <- Vec.unsafeRead (svTrail solver) (lv - 1)
    seq item $ Vec.unsafeWrite (svTrail solver) (lv - 1) (item : xs)
       
getCurrentLevel :: Solver -> IO Level
getCurrentLevel solver = Vec.getSize (svTrail solver)

getLevelGen :: Solver -> Level -> IO Gen
getLevelGen solver lv = Vec.unsafeRead (svLevelGen solver) lv

pushBacktrackPoint :: Solver -> IO ()
pushBacktrackPoint solver = do
  Vec.push (svTrail solver) []
  lv <- getCurrentLevel solver
  size <- Vec.getSize (svLevelGen solver)
  if lv < size then do
    g <- Vec.unsafeRead (svLevelGen solver) lv
    Vec.unsafeWrite (svLevelGen solver) lv (g + 1)
  else
    Vec.push (svLevelGen solver) 0

popBacktrackPoint :: Solver -> IO ()
popBacktrackPoint solver = do
  writeIORef (svIsAfterBacktracking solver) True
  xs <- Vec.unsafePop (svTrail solver)
  forM_ xs $ \item -> do
    case item of
      TrailSetLookup a' b' -> do
        modifyIORef' (svLookupTable solver) (IntMap.adjust (IntMap.delete b') a')
      TrailMerge a' b' a origRootA -> do
        -- Revert changes to Union-Find data strucutres
        ClassUnion _ origClassA origClassB <- Vec.unsafeRead (svClassList solver) b'        
        classForM_ origClassA $ \c -> do
          Vec.unsafeWrite (svRepresentativeTable solver) c a'
        Vec.unsafeWrite (svClassList solver) b' origClassB

        -- Revert changes to proof-forest data strucutres
        let loop c p = do
              tbl <- readIORef (svParent solver)
              writeIORef (svParent solver) (IntMap.update (const p) c tbl)
              unless (c == a) $ do
                let (d, c_eq_d) = tbl IntMap.! c
                loop d (Just (c, c_eq_d))
        loop origRootA Nothing

initAfterBacktracking :: Solver -> IO ()
initAfterBacktracking solver = do
  b <- readIORef (svIsAfterBacktracking solver)
  when b $ do
    writeIORef (svIsAfterBacktracking solver) False
    (defs, _) <- readIORef (svDefs solver)
    forM_ (IntMap.toList defs) $ \(a,(a1,a2)) -> do
      mergeFlatTerm solver (FTApp a1 a2) a

{--------------------------------------------------------------------
  Helper funcions
--------------------------------------------------------------------}

lookup :: Solver -> FSym -> FSym -> IO (Maybe Eqn1)
lookup solver c1 c2 = do
  tbl <- readIORef $ svLookupTable solver
  return $ do
     m <- IntMap.lookup c1 tbl
     IntMap.lookup c2 m

setLookup :: Solver -> FSym -> FSym -> Eqn1 -> IO ()
setLookup solver a1 a2 eqn = do
  modifyIORef' (svLookupTable solver) $
    IntMap.insertWith IntMap.union a1 (IntMap.singleton a2 eqn)  
  addToTrail solver (TrailSetLookup a1 a2)

addToPending :: Solver -> Eqn -> IO ()
addToPending solver eqn = Vec.push (svPending solver) eqn

getRepresentative :: Solver -> FSym -> IO FSym
getRepresentative solver c = Vec.unsafeRead (svRepresentativeTable solver) c

getParent :: Solver -> FSym -> IO (Maybe (FSym, Eqn))
getParent solver c = do
  m <- readIORef $ svParent solver
  return $ IntMap.lookup c m

nearestCommonAncestor :: Solver -> FSym -> FSym -> IO (Maybe FSym)
nearestCommonAncestor solver a b = do
  let loop c !ret = do
        m <- getParent solver c
        case m of
          Nothing -> return ret
          Just (d,_) -> loop d (IntSet.insert d ret)
  a_ancestors <- loop a (IntSet.singleton a)

  let loop2 c = do
        if c `IntSet.member` a_ancestors then
          return (Just c)
        else do
          m <- getParent solver c
          case m of
            Nothing -> return Nothing
            Just (d,_) -> loop2 d
  loop2 b

termToFlatTerm :: Solver -> Term -> IO FlatTerm
termToFlatTerm solver (TApp f xs) = do
  xs' <- mapM (termToFlatTerm solver) xs
  let phi t u = do
        t' <- flatTermToFSym solver t
        u' <- flatTermToFSym solver u
        return $ FTApp t' u'
  foldM phi (FTConst f) xs'

flatTermToFSym :: Solver -> FlatTerm -> IO FSym
flatTermToFSym _ (FTConst c) = return c
flatTermToFSym solver (FTApp c d) = do
  (defs1,defs2) <- readIORef $ svDefs solver
  a <- case Map.lookup (c,d) defs2 of
         Just a -> return a
         Nothing -> do
           a <- newFSym solver
           writeIORef (svDefs solver) (IntMap.insert a (c,d) defs1, Map.insert (c,d) a defs2)
           mergeFlatTerm solver (FTApp c d) a
           return a
  return a

termToFSym :: Solver -> Term -> IO FSym
termToFSym solver t = flatTermToFSym solver =<< termToFlatTerm solver t

maybeToIntSet :: Maybe Int -> IntSet
maybeToIntSet Nothing  = IntSet.empty
maybeToIntSet (Just x) = IntSet.singleton x
